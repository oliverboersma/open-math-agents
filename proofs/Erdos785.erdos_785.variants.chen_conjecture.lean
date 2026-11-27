import FormalConjectures.ErdosProblems.«785»

/-!
A formal proof of Chen's conjecture on additive complements.

The argument follows Zihan Zhang, A Sharp Bound for Additive Complements,
arXiv:2610.29963, Theorem 1.1. Wouter van Doorn, Boning Liu and Quanyu Tang
proved the result independently in On Almost Perfect Additive Complements,
arXiv:2610.35027.

For the Lane A team, Claude Opus 5.5 proved E785.diff_unique,
E785.limsup_bound and E785.bounded_excess with their finite counting helpers.
Claude Fable 5.2 proved E785.gap_transfer with its reflected counting helpers.
GPT-6.2 Astra formalized the large-gap selection, the interval matchings
and rectangle estimates, the final density contradiction, and the assembly.
-/

open Filter Erdos785

namespace E785

/-- Zhang, Lemma 2.2: with unique representations from `n₀` on, two distinct pairs with the same
difference `b - a` involve only elements below `n₀`. -/
theorem diff_unique (A B : Set ℕ) (n₀ : ℕ)
    (hr : ∀ n, n₀ ≤ n → ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n)
    {a b a' b' : ℕ} (ha : a ∈ A) (hb : b ∈ B) (ha' : a' ∈ A) (hb' : b' ∈ B)
    (hne : (a, b) ≠ (a', b')) (hdiff : (b : ℤ) - a = (b' : ℤ) - a') :
    a < n₀ ∧ b < n₀ ∧ a' < n₀ ∧ b' < n₀ := by
  have hsum : a + b' = a' + b := by omega
  have hlt : a + b' < n₀ := by
    by_contra hcon
    obtain ⟨p, -, huniq⟩ := hr (a + b') (by omega)
    have h1 : (a, b') = p := huniq (a, b') ⟨ha, hb', rfl⟩
    have h2 : (a', b) = p := huniq (a', b) ⟨ha', hb, hsum.symm⟩
    have h3 : (a, b') = (a', b) := h1.trans h2.symm
    rw [Prod.mk.injEq] at h3
    apply hne
    rw [h3.1, h3.2]
  omega

/-- The board's limsup hypothesis gives an eventual linear bound with a constant in `(1, 3/2)`
(the paper's (3.1), at natural arguments). -/
theorem limsup_bound (A B : Set ℕ)
    (h : limsup (fun x : ℕ => ((counting A x * counting B x : ℝ) / (x : ℝ) : EReal)) atTop
      < ((3 / 2 : ℝ) : EReal)) :
    ∃ κ : ℝ, 1 < κ ∧ κ < 3 / 2 ∧
      ∀ᶠ x : ℕ in atTop, (counting A x * counting B x : ℝ) ≤ κ * x := by
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp h
  have hc2' : c < 3 / 2 := EReal.coe_lt_coe_iff.mp hc2
  have hk : (5 / 4 : ℝ) ≤ max c (5 / 4) := le_max_right _ _
  refine ⟨max c (5 / 4), by linarith, max_lt hc2' (by norm_num), ?_⟩
  have hlt : limsup (fun x : ℕ => ((counting A x * counting B x : ℝ) / (x : ℝ) : EReal)) atTop
      < ((max c (5 / 4) : ℝ) : EReal) :=
    lt_of_lt_of_le hc1 (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  filter_upwards [eventually_lt_of_limsup_lt hlt, eventually_ge_atTop 1] with x hx hx1
  have hx' : (counting A x * counting B x : ℝ) / (x : ℝ) < max c (5 / 4) :=
    EReal.coe_lt_coe_iff.mp hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  rw [div_lt_iff₀ hxpos] at hx'
  exact hx'.le

open Classical in
/-- The number `r(n)` of pairs `(a, b) ∈ A × B` with `a + b = n`. -/
noncomputable def fr_rep (A B : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n)).card

open Classical in
/-- With `0 ∉ A`, the counting function counts `A ∩ [0, X]`. -/
theorem fr_counting_eq (A : Set ℕ) (hA0 : 0 ∉ A) (X : ℕ) :
    counting A X = ((Finset.range (X + 1)).filter (fun a => a ∈ A)).card := by
  unfold counting
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.coe_filter, Finset.mem_range,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ha, h1, h2⟩
    exact ⟨by omega, ha⟩
  · rintro ⟨h1, ha⟩
    refine ⟨ha, ?_, by omega⟩
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      exact absurd ha hA0
    · exact h

open Classical in
/-- Zhang (2.1): `A(X) B(X) = Σ_{n ≤ X} r(n) + T(X)`. -/
theorem fr_identity (A B : Set ℕ) (hA0 : 0 ∉ A) (hB0 : 0 ∉ B) (X : ℕ) :
    counting A X * counting B X = ∑ n ∈ Finset.range (X + 1), fr_rep A B n +
      ((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ B ∧ X < p.1 + p.2)).card := by
  have hbox : counting A X * counting B X =
      ((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ B)).card := by
    rw [fr_counting_eq A hA0, fr_counting_eq B hB0, Finset.filter_product, Finset.card_product]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ B))
    (fun p : ℕ × ℕ => p.1 + p.2 ≤ X)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hR : ((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p : ℕ × ℕ => (p.1 ∈ A ∧ p.2 ∈ B) ∧ p.1 + p.2 ≤ X)).card =
      ∑ n ∈ Finset.range (X + 1), fr_rep A B n := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1 + p.2)
      (t := Finset.range (X + 1))]
    · apply Finset.sum_congr rfl
      intro n hn
      unfold fr_rep
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hn ⊢
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, ⟨ha, hb⟩, hle⟩, heq⟩
        exact ⟨⟨by omega, by omega⟩, ha, hb, heq⟩
      · rintro ⟨⟨h1, h2⟩, ha, hb, heq⟩
        exact ⟨⟨⟨by omega, by omega⟩, ⟨ha, hb⟩, by omega⟩, heq⟩
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq,
        Finset.coe_range, Set.mem_Iio] at hp ⊢
      omega
  have hT : ((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p : ℕ × ℕ => (p.1 ∈ A ∧ p.2 ∈ B) ∧ ¬ p.1 + p.2 ≤ X)) =
      ((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ B ∧ X < p.1 + p.2)) := by
    ext p
    simp only [Finset.mem_filter, not_le, and_assoc]
  rw [hR, hT] at hsplit
  rw [hbox, ← hsplit]

open Classical in
/-- Every `n ∈ A + B` has at least one representation. -/
theorem fr_rep_pos (A B : Set ℕ) (n : ℕ) (h : ∃ a ∈ A, ∃ b ∈ B, a + b = n) :
    1 ≤ fr_rep A B n := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  unfold fr_rep
  apply Finset.card_pos.mpr
  refine ⟨(a, b), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨by omega, by omega⟩, ha, hb, hab⟩

/-- A monotone bounded sequence of naturals is eventually constant. -/
theorem fr_eventually_const (P : ℕ → ℕ) (hP : Monotone P) (M : ℕ) (hM : ∀ X, P X ≤ M) :
    ∃ X₁, ∀ X, X₁ ≤ X → P X = P X₁ := by
  by_contra hcon0
  have hcon : ∀ X₁, ∃ X, X₁ ≤ X ∧ P X ≠ P X₁ := by
    intro X₁
    by_contra h
    exact hcon0 ⟨X₁, fun X hX => by
      by_contra h'
      exact h ⟨X, hX, h'⟩⟩
  have key : ∀ k, ∃ X, k ≤ P X := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨X, hX⟩ := ih
      obtain ⟨X', hXX', hne⟩ := hcon X
      have := hP hXX'
      exact ⟨X', by omega⟩
  obtain ⟨X, hX⟩ := key (M + 1)
  have := hM X
  omega

open Classical in
/-- Zhang, Lemma 2.1 (after Sarkozy and Szemeredi), in the board's notation: if the excess
`A(x)B(x) - x` does not tend to infinity, then representations are eventually unique, and along
arbitrarily large `X` both the excess and `T(X)`, the number of pairs `(a, b) ∈ A × B` with
`a, b ≤ X < a + b`, stay below a fixed bound. -/
theorem bounded_excess (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (hA0 : 0 ∉ A) (hB0 : 0 ∉ B) (hAB : IsAdditiveComplement A B)
    (hnot : ¬ Tendsto (fun x : ℕ => (counting A x * counting B x : ℝ) - (x : ℝ)) atTop atTop) :
    (∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n, n₀ ≤ n → ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n) ∧
    ∃ K : ℕ, ∃ᶠ X : ℕ in atTop, counting A X * counting B X ≤ X + K ∧
      ((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ B ∧ X < p.1 + p.2)).card ≤ K := by
  -- The excess stays below a fixed natural number along arbitrarily large `X`.
  have hb : ∃ b : ℝ, ∃ᶠ X : ℕ in atTop, (counting A X * counting B X : ℝ) - X < b := by
    by_contra hcon
    apply hnot
    rw [tendsto_atTop]
    intro b
    have h1 : ¬ ∃ᶠ X : ℕ in atTop, (counting A X * counting B X : ℝ) - X < b :=
      fun h => hcon ⟨b, h⟩
    rw [not_frequently] at h1
    filter_upwards [h1] with X hX
    exact not_lt.mp hX
  obtain ⟨b, hb⟩ := hb
  obtain ⟨K₁, hfreq⟩ : ∃ K₁ : ℕ, ∃ᶠ X : ℕ in atTop, counting A X * counting B X ≤ X + K₁ := by
    refine ⟨⌈b⌉₊, hb.mono fun X hX => ?_⟩
    have h2 : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    have h3 : ((counting A X * counting B X : ℕ) : ℝ) < ((X + ⌈b⌉₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact (Nat.cast_lt.mp h3).le
  -- Every `n ≥ N` has a representation.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hAB
  have hrN : ∀ n, N ≤ n → 1 ≤ fr_rep A B n := fun n hn =>
    fr_rep_pos A B n (Set.mem_add.mp (hN n hn))
  have hid := fr_identity A B hA0 hB0
  have hsub : ∀ X M, ∑ n ∈ Finset.Ico M (X + 1), fr_rep A B n ≤
      ∑ n ∈ Finset.range (X + 1), fr_rep A B n := by
    intro X M
    apply Finset.sum_le_sum_of_subset
    intro n hn
    simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢
    exact hn.2
  -- The running sums `P(X) = Σ_{N ≤ n ≤ X} (r(n) - 1)`.
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ, ∀ X, P X = ∑ n ∈ Finset.Ico N (X + 1), (fr_rep A B n - 1) :=
    ⟨_, fun X => rfl⟩
  have hPmono : Monotone P := by
    intro X Y hXY
    rw [hP, hP]
    exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right (by omega))
  have hsumIco : ∀ X, ∑ n ∈ Finset.Ico N (X + 1), fr_rep A B n = P X + (X + 1 - N) := by
    intro X
    have h1 : ∀ n ∈ Finset.Ico N (X + 1), fr_rep A B n = (fr_rep A B n - 1) + 1 := by
      intro n hn
      have := hrN n (Finset.mem_Ico.mp hn).1
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
      smul_eq_mul, mul_one, hP]
  have hPfreq : ∃ᶠ X in atTop, P X ≤ K₁ + N := by
    apply hfreq.mono
    intro X hX
    have h1 := hid X
    have h2 := hsub X N
    have h3 := hsumIco X
    omega
  have hPbdd : ∀ X, P X ≤ K₁ + N := by
    intro X
    obtain ⟨Y, hY, hXY⟩ := (hPfreq.and_eventually (eventually_ge_atTop X)).exists
    exact le_trans (hPmono hXY) hY
  obtain ⟨X₁, hconst⟩ := fr_eventually_const P hPmono (K₁ + N) hPbdd
  -- Hence `r(n) = 1` for all large `n`.
  have hr1 : ∀ n, X₁ + 1 ≤ n → N ≤ n → fr_rep A B n = 1 := by
    intro n hn1 hn2
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e1 := hconst (m + 1) (by omega)
    have e2 := hconst m (by omega)
    have e3 : P (m + 1) = P m + (fr_rep A B (m + 1) - 1) := by
      rw [hP, hP, Finset.sum_Ico_succ_top (by omega : N ≤ m + 1)]
    have e4 := hrN (m + 1) hn2
    omega
  refine ⟨⟨max (X₁ + 1) N, by omega, fun n hn => ?_⟩, ?_⟩
  · have h1 : fr_rep A B n = 1 := hr1 n (by omega) (by omega)
    unfold fr_rep at h1
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    refine ⟨p, ?_, ?_⟩
    · have hmem : p ∈ ({p} : Finset (ℕ × ℕ)) := Finset.mem_singleton_self p
      rw [← hp, Finset.mem_filter] at hmem
      exact hmem.2
    · intro q hq
      obtain ⟨hqa, hqb, hqs⟩ := hq
      have hmem : q ∈ ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n)) := by
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, hqa, hqb, hqs⟩
      rw [hp, Finset.mem_singleton] at hmem
      exact hmem
  · refine ⟨K₁ + max (X₁ + 1) N, hfreq.mono fun X hX => ⟨by omega, ?_⟩⟩
    have h1 := hid X
    have h2 := hsub X (max (X₁ + 1) N)
    have h3 : ∑ n ∈ Finset.Ico (max (X₁ + 1) N) (X + 1), fr_rep A B n =
        X + 1 - max (X₁ + 1) N := by
      rw [Finset.sum_congr rfl (fun n hn => hr1 n
        (le_trans (le_max_left _ _) (Finset.mem_Ico.mp hn).1)
        (le_trans (le_max_right _ _) (Finset.mem_Ico.mp hn).1)),
        Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
    omega

end E785

open Filter Erdos785

namespace E785

/-- Two representations `a + b = a' + b'` of one sum that is at least `n₀` coincide. -/
theorem gt_unique {A B : Set ℕ} {n₀ : ℕ}
    (hr : ∀ n, n₀ ≤ n → ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n)
    {a b a' b' : ℕ} (ha : a ∈ A) (hb : b ∈ B) (ha' : a' ∈ A) (hb' : b' ∈ B)
    (hsum : a + b = a' + b') (hn : n₀ ≤ a + b) : a = a' ∧ b = b' := by
  obtain ⟨p, -, hp⟩ := hr (a + b) hn
  have h1 : (a, b) = p := hp (a, b) ⟨ha, hb, rfl⟩
  have h2 : (a', b') = p := hp (a', b') ⟨ha', hb', hsum.symm⟩
  have h3 : (a, b) = (a', b') := h1.trans h2.symm
  exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

open Classical in
/-- The elements of `A` that are at most `x`. -/
noncomputable def gt_low (A : Set ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (fun a => a ∈ A)

open Classical in
/-- The number of `a ∈ A` with `a ≤ x` and `k + a - x ∈ B`, that is, the number of pairs
`(a, b)` with `a ∈ A`, `a ≤ x`, `b ∈ B` and `b - a = k - x`. -/
noncomputable def gt_cnt (A B : Set ℕ) (x k : ℕ) : ℕ :=
  ((gt_low A x).filter (fun a => x ≤ k + a ∧ k + a - x ∈ B)).card

theorem gt_mem_low {A : Set ℕ} {x a : ℕ} : a ∈ gt_low A x ↔ a ≤ x ∧ a ∈ A := by
  classical
  unfold gt_low
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- Lemma 2.2 in local form: from `x + n₀` on, a difference is represented at most once. -/
theorem gt_cnt_le_one {A B : Set ℕ} {n₀ : ℕ}
    (hr : ∀ n, n₀ ≤ n → ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n)
    {x k : ℕ} (hk : x + n₀ ≤ k) : gt_cnt A B x k ≤ 1 := by
  classical
  unfold gt_cnt
  rw [Finset.card_le_one]
  intro a ha a' ha'
  rw [Finset.mem_filter, gt_mem_low] at ha ha'
  obtain ⟨⟨hax, haA⟩, h1, hbB⟩ := ha
  obtain ⟨⟨hax', haA'⟩, h1', hbB'⟩ := ha'
  exact (gt_unique hr haA hbB' haA' hbB (by omega) (by omega)).1

/-- The key identity (4.4), by double counting: for `x + n₀ ≤ n < y`, the counts
`gt_cnt A B x (n - a)` over the elements `a ≤ x` of `A` add up to the number of those
elements. -/
theorem gt_key {A B : Set ℕ} {n₀ : ℕ}
    (hr : ∀ n, n₀ ≤ n → ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n)
    {x y : ℕ} (hcons : ∀ a ∈ A, x < a → y ≤ a)
    {n : ℕ} (hn : x + n₀ ≤ n) (hny : n < y) :
    ∑ a ∈ gt_low A x, gt_cnt A B x (n - a) = (gt_low A x).card := by
  classical
  unfold gt_cnt
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun a' ha' => ?_)
  rw [gt_mem_low] at ha'
  obtain ⟨⟨p1, p2⟩, ⟨hp1, hp2, hsum⟩, huniq⟩ := hr (n - x + a') (by omega)
  simp only at hp1 hp2 hsum
  have hp1x : p1 ≤ x := by
    by_contra h
    have := hcons p1 hp1 (by omega)
    omega
  rw [Finset.sum_eq_single p1]
  · rw [if_pos]
    refine ⟨by omega, ?_⟩
    have h2 : n - p1 + a' - x = p2 := by omega
    rw [h2]
    exact hp2
  · intro a ha hne
    rw [gt_mem_low] at ha
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hne (congrArg Prod.fst (huniq (a, n - a + a' - x) ⟨ha.2, h2, by omega⟩))
  · intro h
    exact absurd (gt_mem_low.2 ⟨hp1x, hp1⟩) h

/-- The paper's (4.6) and (4.7): every `k` with `n₀ ≤ k ≤ 2 x + n₀ - 1` has
`gt_cnt A B x k = 1`. The index `j` is the distance `2 x + n₀ - 1 - k`, and the induction runs
downward in `k`. -/
theorem gt_cnt_eq_one {A B : Set ℕ} {n₀ : ℕ}
    (hr : ∀ n, n₀ ≤ n → ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n)
    {x y : ℕ} (hxA : x ∈ A) (hcons : ∀ a ∈ A, x < a → y ≤ a) (hy : 3 * x + n₀ ≤ y) :
    ∀ j k : ℕ, n₀ ≤ k → k + j + 1 = 2 * x + n₀ → gt_cnt A B x k = 1 := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro k hk hkj
    have hxS : x ∈ gt_low A x := gt_mem_low.2 ⟨le_refl x, hxA⟩
    have hkey := gt_key hr hcons (n := k + x) (by omega) (by omega)
    rw [← Finset.add_sum_erase _ _ hxS] at hkey
    have hkx : k + x - x = k := by omega
    rw [hkx] at hkey
    have hcard : (gt_low A x).card = ((gt_low A x).erase x).card + 1 := by
      rw [Finset.card_erase_of_mem hxS]
      have hpos : 0 < (gt_low A x).card := Finset.card_pos.2 ⟨x, hxS⟩
      omega
    by_cases hcase : x + n₀ ≤ k
    · have hle : gt_cnt A B x k ≤ 1 := gt_cnt_le_one hr hcase
      have hsum : ∑ a ∈ (gt_low A x).erase x, gt_cnt A B x (k + x - a)
          ≤ ((gt_low A x).erase x).card := by
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_le_sum (fun a ha => ?_)
        have hax := gt_mem_low.1 (Finset.mem_of_mem_erase ha)
        exact gt_cnt_le_one hr (by omega)
      omega
    · have hsum : ∑ a ∈ (gt_low A x).erase x, gt_cnt A B x (k + x - a)
          = ((gt_low A x).erase x).card := by
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl (fun a ha => ?_)
        have hax := gt_mem_low.1 (Finset.mem_of_mem_erase ha)
        have hne := Finset.ne_of_mem_erase ha
        exact ih (j - (x - a)) (by omega) (k + x - a) (by omega) (by omega)
      omega

/-- Zhang, Lemma 4.1: if every `n ≥ n₀` has exactly one representation `a + b` with `a ∈ A`,
`b ∈ B`, and `x < y` are consecutive elements of `A` with `x ≥ 2 n₀` and `y ≥ 3 x + n₀`,
then `B` misses the interval `[y - x + n₀, y + x + n₀ - 1]`. -/
theorem gap_transfer (A B : Set ℕ) (n₀ : ℕ) (hn₀ : 1 ≤ n₀)
    (hr : ∀ n, n₀ ≤ n → ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n)
    {x y : ℕ} (hxA : x ∈ A) (hyA : y ∈ A) (hxy : x < y)
    (hcons : ∀ a ∈ A, x < a → y ≤ a)
    (hx : 2 * n₀ ≤ x) (hy : 3 * x + n₀ ≤ y) :
    ∀ b ∈ B, b < y - x + n₀ ∨ y + x + n₀ - 1 < b := by
  classical
  intro b hb
  by_contra hcon
  have hone : gt_cnt A B x (b + x - y) = 1 :=
    gt_cnt_eq_one hr hxA hcons hy (2 * x + n₀ - 1 - (b + x - y)) (b + x - y)
      (by omega) (by omega)
  have hpos : 0 < gt_cnt A B x (b + x - y) := by omega
  unfold gt_cnt at hpos
  obtain ⟨a', ha'⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_filter, gt_mem_low] at ha'
  obtain ⟨⟨hax, haA⟩, hle, hbB⟩ := ha'
  have huniq := gt_unique hr haA hb hyA hbB (by omega) (by omega)
  omega

end E785

open Filter Erdos785
namespace ChenGap

open Classical in
noncomputable def initial (A : Set ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (· ∈ A)

@[simp] lemma mem_initial {A : Set ℕ} {x a : ℕ} :
    a ∈ initial A x ↔ a ∈ A ∧ a ≤ x := by
  classical
  simp [initial, and_comm]

lemma initial_card {A : Set ℕ} (h0 : 0 ∉ A) (x : ℕ) :
    (initial A x).card = counting A x := by
  rw [← Set.ncard_coe_finset, counting]
  congr 1
  ext a
  simp only [Finset.mem_coe, mem_initial, Set.mem_inter_iff, Set.mem_Icc]
  exact ⟨fun ⟨ha, hl⟩ => ⟨ha, Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha)), hl⟩,
    fun h => ⟨h.1, h.2.2⟩⟩

lemma initial_mono (A : Set ℕ) {x y : ℕ} (h : x ≤ y) : initial A x ⊆ initial A y := by
  intro a ha
  exact mem_initial.mpr ⟨(mem_initial.mp ha).1, (mem_initial.mp ha).2.trans h⟩

lemma initial_large {A : Set ℕ} (hA : A.Infinite) (k : ℕ) :
    ∃ N, ∀ x ≥ N, k ≤ (initial A x).card := by
  obtain ⟨s, hs, hk⟩ := hA.exists_subset_card_eq k
  refine ⟨s.sup id, fun x hx => hk ▸ Finset.card_le_card ?_⟩
  intro a ha
  exact mem_initial.mpr ⟨hs ha, (Finset.le_sup (f := id) ha).trans hx⟩

abbrev UniqueFrom (A B : Set ℕ) (n₀ : ℕ) :=
  ∀ n, n₀ ≤ n → ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n

lemma unique_swap {A B : Set ℕ} {n₀ : ℕ} (h : UniqueFrom A B n₀) : UniqueFrom B A n₀ := by
  intro n hn
  obtain ⟨⟨a,b⟩, ⟨ha,hb,hs⟩, hu⟩ := h n hn
  refine ⟨(b,a), ⟨hb, ha, by simpa [Nat.add_comm] using hs⟩, ?_⟩
  rintro ⟨d,c⟩ ⟨hd,hc,he⟩
  have eq := hu (c,d) ⟨hc, hd, by simpa [Nat.add_comm] using he⟩
  exact congrArg Prod.swap eq

open Classical in
noncomputable def pairAt (A B : Set ℕ) (n : ℕ) : ℕ × ℕ :=
  if h : ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n then h.choose else (0, 0)

lemma pairAt_spec {A B : Set ℕ} {n₀ n : ℕ} (h : UniqueFrom A B n₀) (hn : n₀ ≤ n) :
    (pairAt A B n).1 ∈ A ∧ (pairAt A B n).2 ∈ B ∧ (pairAt A B n).1 + (pairAt A B n).2 = n := by
  classical
  rw [pairAt, dif_pos (h n hn).exists]
  exact (h n hn).exists.choose_spec

lemma rectangle_cover {A B : Set ℕ} {n₀ z u v : ℕ} (h : UniqueFrom A B n₀)
    (hw : ∀ n, n₀ ≤ n → n < z → (pairAt A B n).1 ≤ u ∧ (pairAt A B n).2 ≤ v) :
    z ≤ (initial A u).card * (initial B v).card + n₀ := by
  classical
  have hh : (Finset.Ico n₀ z).card ≤ (initial A u ×ˢ initial B v).card := by
    apply Finset.card_le_card_of_injOn (pairAt A B)
    · intro n hn
      obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hn
      obtain ⟨ha, hb, -⟩ := pairAt_spec h hl
      obtain ⟨hu, hv⟩ := hw n hl hu
      exact Finset.mem_product.mpr ⟨mem_initial.mpr ⟨ha, hu⟩, mem_initial.mpr ⟨hb, hv⟩⟩
    · intro i hi j hj he
      have h₁ := (pairAt_spec h (Finset.mem_Ico.mp hi).1).2.2
      have h₂ := (pairAt_spec h (Finset.mem_Ico.mp hj).1).2.2
      rw [he, h₂] at h₁
      exact h₁.symm
  simp only [Nat.card_Ico, Finset.card_product] at hh
  omega

open Classical in
noncomputable def overflow (A B : Set ℕ) (X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
    (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ B ∧ X < p.1 + p.2))

@[simp] lemma mem_overflow {A B : Set ℕ} {X a b : ℕ} :
    (a,b) ∈ overflow A B X ↔ a ≤ X ∧ b ≤ X ∧ a ∈ A ∧ b ∈ B ∧ X < a + b := by
  classical
  simp [overflow, and_assoc]

lemma overflow_swap (A B : Set ℕ) (X : ℕ) :
    (overflow B A X).card = (overflow A B X).card := by
  apply Finset.card_nbij' Prod.swap Prod.swap
  · rintro ⟨a,b⟩ h
    simpa [mem_overflow, Nat.add_comm, and_comm, and_left_comm, and_assoc] using h
  · rintro ⟨a,b⟩ h
    simpa [mem_overflow, Nat.add_comm, and_comm, and_left_comm, and_assoc] using h
  · intro p _
    exact Prod.swap_swap p
  · intro p _
    exact Prod.swap_swap p

lemma tail_count {A B : Set ℕ} {X w b : ℕ} (hw : w ≤ X) (hb : b ∈ initial B X)
    (hcover : X ≤ w + b) :
    (initial A X).card ≤ (initial A w).card + (overflow A B X).card := by
  classical
  have hs := Finset.card_sdiff_add_card_eq_card (initial_mono A hw)
  have hinj : (initial A X \ initial A w).card ≤ (overflow A B X).card := by
    apply Finset.card_le_card_of_injOn (fun a => (a,b))
    · intro a ha
      obtain ⟨hi,ho⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨hA, haX⟩ := mem_initial.mp hi
      have hw' : w < a := by
        by_contra! hc
        exact ho (mem_initial.mpr ⟨hA, hc⟩)
      exact mem_overflow.mpr ⟨haX, (mem_initial.mp hb).2, hA, (mem_initial.mp hb).1, by omega⟩
    · intro a _ a' _ he
      exact congrArg Prod.fst he
  omega

/-- An integer margin in the strict upper density bound. -/
lemma integer_bound {A B : Set ℕ} (ha : 0 ∉ A) (hb : 0 ∉ B) {κ : ℝ}
    (hk : κ < 3 / 2)
    (hc : ∀ᶠ x : ℕ in atTop, (counting A x * counting B x : ℝ) ≤ κ * x) :
    ∃ D N : ℕ, 0 < D ∧ ∀ x ≥ N,
      2 * D * ((initial A x).card * (initial B x).card) + x ≤ 3 * D * x := by
  have hpos : 0 < 3 - 2 * κ := by linarith
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / (3 - 2 * κ))
  have hq' := (div_lt_iff₀ hpos).mp hq
  have hD : 0 < q := by
    by_contra! hz
    have hzero : q = 0 := by omega
    norm_num [hzero] at hq'
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  refine ⟨q, N, hD, fun x hx => ?_⟩
  rw [initial_card ha, initial_card hb]
  have hh := mul_le_mul_of_nonneg_left (hN x hx) (show 0 ≤ 2 * (q : ℝ) by positivity)
  have hh' := mul_le_mul_of_nonneg_right hq'.le (show (0 : ℝ) ≤ x by positivity)
  exact_mod_cast (show 2 * (q : ℝ) * (counting A x * counting B x : ℝ) + x ≤ 3 * q * x by
    nlinarith only [hh, hh'])

end ChenGap

open Filter
namespace ChenGap

/-- Consecutive elements from an arbitrarily prescribed lower endpoint onward. -/
def HasGap (A : Set ℕ) (n₀ L : ℕ) : Prop :=
  ∃ x y, L ≤ x ∧ x ∈ A ∧ y ∈ A ∧ x < y ∧
    (∀ a ∈ A, x < a → y ≤ a) ∧ 3 * x + n₀ ≤ y

/-- The quantitative estimate used both at half the sample and at its distance from a maximum. -/
lemma trimmed_rectangle {D K n₀ X w m n a b : ℕ}
    (hX : 64 * D * n₀ + 16 * K + 64 ≤ X) (hhalf : X ≤ 2 * w + 1)
    (hm : 32 * D * K ≤ m) (hn : 32 * D * K ≤ n)
    (hlo : X ≤ m * n + n₀) (hhi : m * n ≤ X + K)
    (ha : a ≤ m) (hma : m ≤ a + K) (hnb : n ≤ b + K)
    (hcap : 2 * D * (a * b) + w ≤ 3 * D * w) :
    2 * X + n₀ < 3 * w := by
  by_contra! he
  have htrim : X ≤ a * b + K * (m + n) + n₀ := by
    nlinarith only [hlo, Nat.mul_le_mul_right n hma, Nat.mul_le_mul_left a hnb,
      Nat.mul_le_mul_right K ha]
  -- Each lost row or column costs at most K entries per element of the other side.
  -- Both error terms can be absorbed because each side has at least 32 D K elements.
  have hem := (Nat.mul_le_mul_left m hn).trans hhi
  have hen := (Nat.mul_le_mul_right n hm).trans hhi
  nlinarith only [Nat.mul_le_mul_left (2 * D) htrim, Nat.mul_le_mul_left D he,
    hcap, hem, hen, hhalf, hX]

lemma gap_from_max {A B : Set ℕ} (hA : A.Infinite) {X x L n₀ K : ℕ}
    (hL : L ≤ x) (hx : x ∈ initial A X) (hmax : ∀ a ∈ initial A X, a ≤ x)
    (hshort : x ≤ X / 2) (hT : (overflow B A X).card ≤ K)
    (htrim : ∀ w, X / 2 ≤ w → w ≤ X →
      (initial A X).card ≤ (initial A w).card + K →
      (initial B X).card ≤ (initial B w).card + K → 2 * X + n₀ < 3 * w) :
    HasGap A n₀ L := by
  classical
  have hw : X / 2 ≤ X - x := by omega
  have hm : initial A X ⊆ initial A (X - x) := by
    intro a ha
    exact mem_initial.mpr ⟨(mem_initial.mp ha).1, (hmax a ha).trans (by omega)⟩
  have hb := tail_count (A := B) (Nat.sub_le X x) hx (show X ≤ X - x + x by omega)
  have hc := htrim (X - x) hw (Nat.sub_le X x)
    ((Finset.card_le_card hm).trans (Nat.le_add_right _ _)) (by omega)
  have hex : ∃ y, y ∈ A ∧ X < y := hA.exists_gt X
  obtain ⟨hy, hXy⟩ := Nat.find_spec hex
  refine ⟨x, Nat.find hex, hL, (mem_initial.mp hx).1, hy, by omega, ?_, by omega⟩
  intro a ha hxa
  apply Nat.find_min' hex
  refine ⟨ha, ?_⟩
  by_contra! he
  exact (Nat.not_le_of_gt hxa) (hmax a (mem_initial.mpr ⟨ha, he⟩))

/-- Zhang's Lemma 3.1, choosing the orientation at each prescribed cutoff. -/
lemma large_gap {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) {n₀ D N K : ℕ}
    (hr : UniqueFrom A B n₀)
    (hc : ∀ x ≥ N, 2 * D * ((initial A x).card * (initial B x).card) + x ≤ 3 * D * x)
    (hsample : ∃ᶠ X : ℕ in atTop, (initial A X).card * (initial B X).card ≤ X + K ∧
      (overflow A B X).card ≤ K) (L : ℕ) :
    HasGap A n₀ L ∨ HasGap B n₀ L := by
  classical
  obtain ⟨c, hcA, hcL⟩ := hA.exists_gt L
  obtain ⟨d, hdB, hdL⟩ := hB.exists_gt L
  obtain ⟨M, hM⟩ := initial_large hA (32 * D * K)
  obtain ⟨M', hM'⟩ := initial_large hB (32 * D * K)
  obtain ⟨X, hX, hprod, hT⟩ := frequently_atTop.1 hsample
    (c + d + M + M' + 2 * N + (64 * D * n₀ + 16 * K + 64))
  have hlo := rectangle_cover (z := X) (u := X) (v := X) hr (by
    intro z hz hzX
    have hh := (pairAt_spec hr hz).2.2
    omega)
  have trim : ∀ w, X / 2 ≤ w → w ≤ X →
      (initial A X).card ≤ (initial A w).card + K →
      (initial B X).card ≤ (initial B w).card + K → 2 * X + n₀ < 3 * w := by
    intro w hw hwX ha hb
    exact trimmed_rectangle (by omega) (by omega) (hM X (by omega)) (hM' X (by omega))
      hlo hprod (Finset.card_le_card (initial_mono A hwX)) ha hb (hc w (by omega))
  have hcI : c ∈ initial A X := mem_initial.mpr ⟨hcA, by omega⟩
  have hdI : d ∈ initial B X := mem_initial.mpr ⟨hdB, by omega⟩
  let x := (initial A X).max' ⟨c, hcI⟩
  let u := (initial B X).max' ⟨d, hdI⟩
  have hx : x ∈ initial A X := Finset.max'_mem _ _
  have hu : u ∈ initial B X := Finset.max'_mem _ _
  have hmax : ∀ a ∈ initial A X, a ≤ x := fun a h => Finset.le_max' _ a h
  have humax : ∀ b ∈ initial B X, b ≤ u := fun b h => Finset.le_max' _ b h
  have hT' : (overflow B A X).card ≤ K := by rwa [overflow_swap]
  by_cases hshort : x ≤ X / 2
  · exact Or.inl (gap_from_max hA (hcL.le.trans (hmax c hcI)) hx hmax hshort hT' trim)
  by_cases hshort' : u ≤ X / 2
  · exact Or.inr (gap_from_max hB (hdL.le.trans (humax d hdI)) hu humax hshort' hT
      fun w hl hh hb ha => trim w hl hh ha hb)
  have ha := tail_count (A := A) (Nat.div_le_self X 2) hu (show X ≤ X/2 + u by omega)
  have hb := tail_count (A := B) (Nat.div_le_self X 2) hx (show X ≤ X/2 + x by omega)
  have hh := trim (X/2) le_rfl (Nat.div_le_self X 2) (by omega) (by omega)
  omega

end ChenGap

namespace ChenGap

/-- Lower half of Zhang's first counting estimate. A representation above the gap
matches each old element away from both boundary intervals with a new element. -/
lemma count_after_lower {A B : Set ℕ} {n₀ x y t : ℕ}
    (hn : 1 ≤ n₀) (hr : UniqueFrom A B n₀) (ht : t ≤ x) (hxy : x < y)
    (hcons : ∀ a ∈ A, x < a → y ≤ a) (hy : 3 * x + n₀ ≤ y)
    (hg : ∀ b ∈ B, b < y - x + n₀ ∨ y + x + n₀ - 1 < b) :
    (initial A x).card + (initial A t).card ≤ (initial A (y + t)).card + 2 * n₀ := by
  classical
  let core := (initial A t).filter (fun a => n₀ ≤ a ∧ a + n₀ ≤ t)
  let fresh := initial A (y + t) \ initial A x
  have hboundary : initial A t ⊆ core ∪ (Finset.range n₀ ∪ Finset.Ioc (t - n₀) t) := by
    intro a ha
    obtain ⟨haA, hat⟩ := mem_initial.mp ha
    by_cases hsmall : a < n₀
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_range.mpr hsmall))
    by_cases hlarge : a + n₀ ≤ t
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, by omega, hlarge⟩)
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨by omega, hat⟩))
  have hcard := (Finset.card_le_card hboundary).trans (Finset.card_union_le _ _)
  have hedge := Finset.card_union_le (Finset.range n₀) (Finset.Ioc (t - n₀) t)
  simp only [Finset.card_range, Nat.card_Ioc] at hedge
  let f := fun a => pairAt A B (y + t - a)
  have hrep : ∀ a ∈ core, (f a).1 ∈ A ∧ (f a).2 ∈ B ∧
      (f a).1 + (f a).2 + a = y + t ∧ y ≤ (f a).1 := by
    intro a ha
    obtain ⟨hi, h₁, h₂⟩ := Finset.mem_filter.mp ha
    have hat := (mem_initial.mp hi).2
    have ⟨hA, hB, hsum⟩ := pairAt_spec hr (n := y + t - a) (by omega)
    change (f a).1 + (f a).2 = y + t - a at hsum
    refine ⟨hA, hB, by omega, ?_⟩
    apply hcons (f a).1 hA
    rcases hg (f a).2 hB with h | h <;> omega
  have hmatch : core.card ≤ fresh.card := by
    apply Finset.card_le_card_of_injOn (fun a => (f a).1)
    · intro a ha
      change (f a).1 ∈ fresh
      obtain ⟨hA, -, hsum, hnew⟩ := hrep a ha
      exact Finset.mem_sdiff.mpr ⟨mem_initial.mpr ⟨hA, by omega⟩,
        fun hi => (show x < (f a).1 by omega).not_ge (mem_initial.mp hi).2⟩
    · intro a ha c hc he
      change (f a).1 = (f c).1 at he
      obtain ⟨haI, hamin, -⟩ := Finset.mem_filter.mp ha
      obtain ⟨hcI, -, -⟩ := Finset.mem_filter.mp hc
      obtain ⟨-, hb, hsum, -⟩ := hrep a ha
      obtain ⟨-, hd, hsum', -⟩ := hrep c hc
      have eq : (a, (f a).2) = (c, (f c).2) :=
        (hr (a + (f a).2) (by omega)).unique
          ⟨(mem_initial.mp haI).1, hb, rfl⟩
          ⟨(mem_initial.mp hcI).1, hd, by change c + (f c).2 = a + (f a).2; omega⟩
      exact congrArg Prod.fst eq
  have hsplit : fresh.card + (initial A x).card = (initial A (y + t)).card :=
    Finset.card_sdiff_add_card_eq_card (initial_mono A (by omega))
  omega

/-- Reverse matching for the upper half of the first estimate. -/
lemma count_after_upper {A B : Set ℕ} {n₀ x y t : ℕ}
    (hr : UniqueFrom A B n₀) (hxy : x < y)
    (hcons : ∀ a ∈ A, x < a → y ≤ a) (hy : n₀ ≤ y) :
    (initial A (y + t)).card ≤ (initial A x).card + (initial A t).card + n₀ := by
  classical
  let fresh := initial A (y + t) \ initial A x
  let core := fresh.filter (fun c => c + n₀ ≤ y + t)
  have hnew : ∀ c ∈ fresh, c ∈ A ∧ y ≤ c ∧ c ≤ y + t := by
    intro c hc
    obtain ⟨hu, hl⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨hcA, ht'⟩ := mem_initial.mp hu
    refine ⟨hcA, hcons _ hcA ?_, ht'⟩
    by_contra! he
    exact hl (mem_initial.mpr ⟨hcA, he⟩)
  have hsubset : fresh ⊆ core ∪ Finset.Ioc (y + t - n₀) (y + t) := by
    intro c hc
    by_cases he : c + n₀ ≤ y + t
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, he⟩)
    exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨by omega, (hnew c hc).2.2⟩)
  have hb := (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  simp only [Nat.card_Ioc] at hb
  let f := fun c => pairAt A B (y + t - c)
  have hrep : ∀ c ∈ core, c ∈ A ∧ (f c).1 ∈ initial A t ∧ (f c).2 ∈ B ∧
      c + (f c).1 + (f c).2 = y + t := by
    intro c hc
    obtain ⟨hf, hl⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcA, hyc, hc'⟩ := hnew c hf
    have ⟨hA, hB, hs⟩ := pairAt_spec hr (n := y + t - c) (by omega)
    change (f c).1 + (f c).2 = y + t - c at hs
    exact ⟨hcA, mem_initial.mpr ⟨hA, by omega⟩, hB, by omega⟩
  have hmatch : core.card ≤ (initial A t).card := by
    apply Finset.card_le_card_of_injOn (fun c => (f c).1)
    · intro c hc
      exact (hrep c hc).2.1
    · intro c hc d hd he
      change (f c).1 = (f d).1 at he
      obtain ⟨hcA, _, hB, hs⟩ := hrep c hc
      obtain ⟨hdA, _, hB',hs'⟩ := hrep d hd
      have hyc := (hnew c (Finset.mem_filter.mp hc).1).2.1
      have eq : (c, (f c).2) = (d, (f d).2) :=
        (hr (c + (f c).2) (by omega)).unique ⟨hcA, hB, rfl⟩ ⟨hdA, hB',by change d + (f d).2 = c + (f c).2; omega⟩
      exact congrArg Prod.fst eq
  have hsplit : fresh.card + (initial A x).card = (initial A (y + t)).card :=
    Finset.card_sdiff_add_card_eq_card (initial_mono A (by omega))
  omega

/-- The rectangle covers every sum in [n₀,y). Its large sums occur once and
the exceptional pairs both have coordinates below n₀. -/
lemma gap_rectangle {A B : Set ℕ} {n₀ x y t : ℕ}
    (hn : 1 ≤ n₀) (hr : UniqueFrom A B n₀) (ht : t ≤ x) (hxy : x < y)
    (hcons : ∀ a ∈ A, x < a → y ≤ a)
    (hg : ∀ b ∈ B, b < y - x + n₀ ∨ y + x + n₀ - 1 < b) :
    y ≤ (initial A x).card * (initial B (y + t)).card + n₀ ∧
    (initial A x).card * (initial B (y + t)).card ≤ y + n₀ + n₀ * n₀ := by
  classical
  constructor
  · apply rectangle_cover hr
    intro n hl hu
    obtain ⟨hA, hB, hs⟩ := pairAt_spec hr hl
    refine ⟨?_, by omega⟩
    by_contra! he
    have hh := hcons _ hA he
    omega
  · let small := Finset.range n₀ ×ˢ Finset.range n₀
    let runs := (Finset.range (y + n₀)).image (pairAt A B)
    have hsub : initial A x ×ˢ initial B (y + t) ⊆ small ∪ runs := by
      rintro ⟨a, b⟩ hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      obtain ⟨haA, hax⟩ := mem_initial.mp ha
      obtain ⟨hbB, hbt⟩ := mem_initial.mp hb
      by_cases hlow : a + b < n₀
      · exact Finset.mem_union_left _ (Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩)
      apply Finset.mem_union_right _
      apply Finset.mem_image.mpr
      refine ⟨a + b, Finset.mem_range.mpr ?_, ?_⟩
      · rcases hg b hbB with h | h <;> omega
      · exact (hr _ (by omega : n₀ ≤ a + b)).unique (pairAt_spec hr (by omega)) ⟨haA, hbB, rfl⟩
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hruns : runs.card ≤ y + n₀ := by
      simpa [runs] using (Finset.card_image_le (s := Finset.range (y + n₀)) (f := pairAt A B))
    simp only [small, Finset.card_product, Finset.card_range] at hcard
    omega

end ChenGap

open Filter Erdos785
namespace ChenGap

/-- Section 5 with an explicit cutoff in place of a limiting sequence. -/
lemma endpoint_contradiction {D n₀ x y m a b : ℕ}
    (hD : 0 < D) (hx : 16 * D * n₀ + 1 ≤ x) (hy : 3 * x ≤ y)
    (hm : 32 * D * n₀ ≤ m) (hma : m ≤ a) (hdouble : 2 * m ≤ a + 2 * n₀)
    (hrect : y ≤ m * b + n₀) (hcap : 2 * D * (a * b) + (y + x) ≤ 3 * D * (y + x)) : False := by
  have hab : a * b ≤ 2 * (y + x) := by
    refine Nat.le_of_mul_le_mul_left ?_ hD
    nlinarith only [hcap, Nat.zero_le (D * (y + x)), Nat.zero_le (y + x)]
  -- The density cap controls the error incurred by losing at most 2 n₀ elements.
  have hsmall := (Nat.mul_le_mul_right b (hm.trans hma)).trans hab
  have hl : 2 * (m * b) ≤ a * b + 2 * n₀ * b := by
    nlinarith only [Nat.mul_le_mul_right b hdouble]
  nlinarith only [Nat.mul_le_mul_left (2 * D) hl, Nat.mul_le_mul_left (4 * D) hrect,
    Nat.mul_le_mul_left D hy, hcap, hsmall, hx, Nat.zero_le y]

lemma rule_out_gap {A B : Set ℕ} {D n₀ N L : ℕ}
    (hD : 0 < D) (hn : 1 ≤ n₀) (hr : UniqueFrom A B n₀)
    (hc : ∀ z ≥ N, 2 * D * ((initial A z).card * (initial B z).card) + z ≤ 3 * D * z)
    (hL₁ : 2 * n₀ ≤ L) (hL₂ : N ≤ L) (hL₃ : 16 * D * n₀ + 1 ≤ L)
    (hbig : ∀ x ≥ L, 32 * D * n₀ ≤ (initial A x).card) (hgap : HasGap A n₀ L) : False := by
  obtain ⟨x, y, hL, hx, hy, hxy, hcons, hlong⟩ := hgap
  have hg := E785.gap_transfer A B n₀ hn hr hx hy hxy hcons (hL₁.trans hL) hlong
  have h₁ := count_after_lower hn hr (t := x) le_rfl hxy hcons hlong hg
  have h₂ := (gap_rectangle hn hr (t := x) le_rfl hxy hcons hg).1
  exact endpoint_contradiction hD (hL₃.trans hL) (by omega) (hbig x hL)
    (Finset.card_le_card (initial_mono A (show x ≤ y + x by omega))) (by omega) h₂
    (hc (y + x) (by omega))

end ChenGap

open ChenGap

theorem OMA.solution : type_of% @Erdos785.erdos_785.variants.chen_conjecture := by
  classical
  intro A B hA hB hA0 hB0 hAB hlim
  by_contra hnot
  obtain ⟨κ, -, hk, hκ⟩ := E785.limsup_bound A B hlim
  obtain ⟨D, N, hD, hc⟩ := integer_bound hA0 hB0 hk hκ
  obtain ⟨⟨n₀, hn, hr⟩, K, hfreq⟩ := E785.bounded_excess A B hA hB hA0 hB0 hAB hnot
  have hs : ∃ᶠ X : ℕ in atTop, (initial A X).card * (initial B X).card ≤ X + K ∧
      (overflow A B X).card ≤ K := by
    apply hfreq.mono
    intro X h
    rw [initial_card hA0, initial_card hB0]
    exact h
  obtain ⟨P, hP⟩ := initial_large hA (32 * D * n₀)
  obtain ⟨Q, hQ⟩ := initial_large hB (32 * D * n₀)
  let L := N + P + Q + 2 * n₀ + (16 * D * n₀ + 1)
  have hL₁ : 2 * n₀ ≤ L := by dsimp [L]; omega
  have hL₂ : N ≤ L := by dsimp [L]; omega
  have hL₃ : 16 * D * n₀ + 1 ≤ L := by dsimp [L]; omega
  rcases large_gap hA hB hr hc hs L with h | h
  · exact rule_out_gap hD hn hr hc hL₁ hL₂ hL₃ (fun x hx => hP x (by dsimp [L] at hx; omega)) h
  · have hc' : ∀ z ≥ N, 2 * D * ((initial B z).card * (initial A z).card) + z ≤ 3 * D * z := by
      intro z hz
      rw [Nat.mul_comm (initial B z).card (initial A z).card]
      exact hc z hz
    exact rule_out_gap hD hn (unique_swap hr) hc' hL₁ hL₂ hL₃
      (fun x hx => hQ x (by dsimp [L] at hx; omega)) h
