import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R1

/-!
# Dyadic counting bound for finite Sidon sets (Erdős Problem 1191, step R1.H1)

For any Sidon set `S ⊆ [1, 2^(2R)]` with `R ≥ 16`, some dyadic scale `k ∈ [R, 2R]`
satisfies `|S ∩ [1, 2^k]|^2 * k ≤ 512 * 2^k`, proved via short-interval Sidon
second-moment counting, dyadic Abel summation, and Cauchy--Schwarz.
-/

-- Problem: Erdős Problem 1191 — reduction step R1.H1
-- Credit: @Ronandt (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real Finset

open scoped Classical

namespace OMA.Erdos1191H1

lemma sidon_diff_inj {A : Set ℕ} (hA : IsSidon A)
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (heq : b₁ - a₁ = b₂ - a₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hsum : b₁ + a₂ = b₂ + a₁ := by omega
  rcases hA b₁ hb₁ b₂ hb₂ a₂ ha₂ a₁ ha₁ hsum with ⟨hb, ha⟩ | ⟨hba, _⟩
  · exact ⟨ha.symm, hb⟩
  · omega

noncomputable def sidonCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (· ∈ A)).card

lemma sidonCount_mul_pred_le {A : Set ℕ} (hA : IsSidon A) (n : ℕ) :
    sidonCount A n * (sidonCount A n - 1) ≤ 2 * n := by
  let S : Finset ℕ := (Finset.Icc 1 n).filter (· ∈ A)
  let P : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun p => p.1 < p.2)
  have hP_le : P.card ≤ n := by
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, P, Finset.mem_filter, Finset.mem_product, S] at hp₁ hp₂
      have ⟨h1, h2⟩ := sidon_diff_inj hA hp₁.1.1.2 hp₁.1.2.2 hp₂.1.1.2 hp₂.1.2.2 hp₁.2 hp₂.2 heq
      exact Prod.ext h1 h2
    have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ))
        (Finset.Icc 1 n : Set ℕ) := by
      intro p hp
      simp only [Finset.mem_coe, P, Finset.mem_filter, Finset.mem_product, S,
        Finset.mem_Icc] at hp ⊢
      omega
    have hle := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2 - p.1) hmaps hinj
    simpa using hle
  have h2P : 2 * P.card = S.card * (S.card - 1) := by
    let Q : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun p => p.2 < p.1)
    have hdisj : Disjoint P Q := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega
    have hunion : P ∪ Q = S.offDiag := by
      ext ⟨a, b⟩
      simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
      constructor
      · rintro (⟨⟨ha, hb⟩, hlt⟩ | ⟨⟨ha, hb⟩, hlt⟩)
        · exact ⟨ha, hb, ne_of_lt hlt⟩
        · exact ⟨ha, hb, ne_of_gt hlt⟩
      · rintro ⟨ha, hb, hne⟩
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Or.inl ⟨⟨ha, hb⟩, hlt⟩
        · exact Or.inr ⟨⟨ha, hb⟩, hlt⟩
    have hPQ : P.card = Q.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hq ⊢
        exact ⟨(q.2, q.1), ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
    have hoff : S.offDiag.card = S.card * S.card - S.card := Finset.offDiag_card S
    have hcard : P.card + Q.card = S.offDiag.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hmul : S.card * (S.card - 1) = S.card * S.card - S.card := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    omega
  change S.card * (S.card - 1) ≤ 2 * n
  omega

lemma sidonCount_le_two_sqrt {A : Set ℕ} (hA : IsSidon A) {n : ℕ} (hn : 1 ≤ n) :
    (sidonCount A n : ℝ) ≤ 2 * Real.sqrt n := by
  have h1 : sidonCount A n * (sidonCount A n - 1) ≤ 2 * n := sidonCount_mul_pred_le hA n
  have hsq : sidonCount A n ^ 2 ≤ 4 * n := by
    rcases Nat.lt_or_ge (sidonCount A n) 2 with hk | hk
    · have : sidonCount A n ≤ 1 := by omega
      nlinarith
    · have h2 : sidonCount A n ≤ 2 * (sidonCount A n - 1) := by omega
      nlinarith
  have hsqR : ((sidonCount A n : ℝ)) ^ 2 ≤ (2 * Real.sqrt n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
    exact_mod_cast hsq
  nlinarith [Real.sqrt_nonneg n]

lemma sidon_window_sq_sum_le {A : Set ℕ} (hA : IsSidon A) {r : ℕ} (hr : 1 ≤ r) :
    ∑ j ∈ Finset.Icc 1 (r ^ 2), (((Finset.Ioc j (j + r)).filter (· ∈ A)).card) ^ 2 ≤
      5 * r ^ 2 := by
  let W : ℕ → Finset ℕ := fun j => (Finset.Ioc j (j + r)).filter (· ∈ A)
  let P : ℕ → Finset (ℕ × ℕ) := fun j => (W j ×ˢ W j).filter (fun p => p.1 < p.2)
  have hpair_sum : ∑ j ∈ Finset.Icc 1 (r ^ 2), (P j).card ≤ r ^ 2 := by
    rw [← Finset.card_sigma]
    let T := (Finset.Icc 1 (r ^ 2)).sigma P
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ × ℕ => (x.2.2 - x.2.1, x.2.1 - x.1)) (T : Set _) := by
      intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_coe, T, Finset.mem_sigma, P, W, Finset.mem_filter,
        Finset.mem_product, Finset.mem_Ioc] at hx₁ hx₂
      have hdiff : x₁.2.2 - x₁.2.1 = x₂.2.2 - x₂.2.1 := congrArg Prod.fst heq
      have hshift : x₁.2.1 - x₁.1 = x₂.2.1 - x₂.1 := congrArg Prod.snd heq
      have ⟨ha, hb⟩ := sidon_diff_inj hA hx₁.2.1.1.2 hx₁.2.1.2.2 hx₂.2.1.1.2 hx₂.2.1.2.2
        hx₁.2.2 hx₂.2.2 hdiff
      have hj : x₁.1 = x₂.1 := by omega
      cases x₁; cases x₂
      simp only at ha hb hj
      subst hj
      exact congrArg (Sigma.mk _) (Prod.ext ha hb)
    have hmaps : Set.MapsTo (fun x : Σ _ : ℕ, ℕ × ℕ => (x.2.2 - x.2.1, x.2.1 - x.1)) (T : Set _)
        ((Finset.Icc 1 r ×ˢ Finset.Icc 1 r : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro x hx
      simp only [Finset.mem_coe, T, Finset.mem_sigma, P, W, Finset.mem_filter,
        Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    have hle := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa [T, sq] using hle
  have hlin_sum : ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card ≤ sidonCount A (r ^ 2 + r) * r := by
    rw [← Finset.card_sigma]
    let T₁ := (Finset.Icc 1 (r ^ 2)).sigma W
    let S := (Finset.Icc 1 (r ^ 2 + r)).filter (· ∈ A)
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ => (x.2, x.2 - x.1)) (T₁ : Set _) := by
      intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_coe, T₁, Finset.mem_sigma, W, Finset.mem_filter,
        Finset.mem_Ioc] at hx₁ hx₂
      have ha : x₁.2 = x₂.2 := congrArg Prod.fst heq
      have hshift : x₁.2 - x₁.1 = x₂.2 - x₂.1 := congrArg Prod.snd heq
      have hj : x₁.1 = x₂.1 := by omega
      cases x₁; cases x₂
      simp only at ha hj
      subst hj; subst ha; rfl
    have hmaps : Set.MapsTo (fun x : Σ _ : ℕ, ℕ => (x.2, x.2 - x.1)) (T₁ : Set _)
        ((S ×ˢ Finset.Icc 1 r : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro x hx
      simp only [Finset.mem_coe, T₁, Finset.mem_sigma, W, S, Finset.mem_filter,
        Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
      exact ⟨⟨⟨by omega, by omega⟩, hx.2.2⟩, ⟨by omega, by omega⟩⟩
    have hle := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa [T₁, sidonCount, S] using hle
  have hcnt : sidonCount A (r ^ 2 + r) ≤ 3 * r := by
    have h1 := sidonCount_mul_pred_le hA (r ^ 2 + r)
    have hr2 : r ≤ r ^ 2 := Nat.le_self_pow (by norm_num) r
    by_contra hgt
    have hge : 3 * r + 1 ≤ sidonCount A (r ^ 2 + r) := by omega
    have hge1 : 3 * r ≤ sidonCount A (r ^ 2 + r) - 1 := by omega
    have hmul : (3 * r + 1) * (3 * r) ≤ sidonCount A (r ^ 2 + r) * (sidonCount A (r ^ 2 + r) - 1) :=
      Nat.mul_le_mul hge hge1
    nlinarith
  have hsq_decomp : ∀ j, (W j).card ^ 2 = 2 * (P j).card + (W j).card := by
    intro j
    let Q := (W j ×ˢ W j).filter (fun p => p.2 < p.1)
    have hdisj : Disjoint (P j) Q := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega
    have hunion : P j ∪ Q = (W j).offDiag := by
      ext ⟨a, b⟩
      simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
      constructor
      · rintro (⟨⟨ha, hb⟩, hlt⟩ | ⟨⟨ha, hb⟩, hlt⟩)
        · exact ⟨ha, hb, ne_of_lt hlt⟩
        · exact ⟨ha, hb, ne_of_gt hlt⟩
      · rintro ⟨ha, hb, hne⟩
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Or.inl ⟨⟨ha, hb⟩, hlt⟩
        · exact Or.inr ⟨⟨ha, hb⟩, hlt⟩
    have hPQ : (P j).card = Q.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hq ⊢
        exact ⟨(q.2, q.1), ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
    have hoff : (W j).offDiag.card = (W j).card * (W j).card - (W j).card := Finset.offDiag_card (W j)
    have hcard : (P j).card + Q.card = (W j).offDiag.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hle : (W j).card ≤ (W j).card * (W j).card := Nat.le_mul_self _
    rw [sq]
    omega
  have hsum_eq : ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card ^ 2 =
      2 * (∑ j ∈ Finset.Icc 1 (r ^ 2), (P j).card) +
        ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card := by
    simp_rw [hsq_decomp, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum_eq]
  have hlin' : ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card ≤ 3 * r ^ 2 := by
    calc ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card
        ≤ sidonCount A (r ^ 2 + r) * r := hlin_sum
      _ ≤ (3 * r) * r := Nat.mul_le_mul_right r hcnt
      _ = 3 * r ^ 2 := by ring
  omega

lemma abel_sum (S b : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N) :
    ∑ k ∈ Finset.Ioc M N, (S k - S (k - 1)) * b k =
      S N * b N - S M * b M + ∑ k ∈ Finset.Ico M N, S k * (b k - b (k + 1)) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    have hIoc : Finset.Ioc M (N + 1) = insert (N + 1) (Finset.Ioc M N) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hIco : Finset.Ico M (N + 1) = insert N (Finset.Ico M N) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hIoc, Finset.sum_insert (by simp), hIco, Finset.sum_insert (by simp), ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma harmonic_Icc_le_log {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    ∑ k ∈ Finset.Icc M N, (1 / (k : ℝ)) ≤ Real.log (N : ℝ) := by
  have htel : ∑ k ∈ Finset.Icc M N, (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) =
      Real.log (N : ℝ) - Real.log ((M - 1 : ℕ) : ℝ) := by
    induction N, hMN using Nat.le_induction with
    | base => simp
    | succ N hMN ih =>
      have hIcc : Finset.Icc M (N + 1) = insert (N + 1) (Finset.Icc M N) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert (by simp), ih]
      simp only [Nat.add_sub_cancel]
      ring
  have hstep : ∑ k ∈ Finset.Icc M N, (1 / (k : ℝ)) ≤
      ∑ k ∈ Finset.Icc M N, (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 : 2 ≤ k := by simp only [Finset.mem_Icc] at hk; omega
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    have hk1pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have h1 := Real.log_le_sub_one_of_pos (div_pos hk1pos hkpos)
    rw [Real.log_div hk1pos.ne' hkpos.ne'] at h1
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have h2 : ((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
      rw [hcast]
      field_simp
      ring
    linarith
  have hlog_nonneg : 0 ≤ Real.log ((M - 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M - 1))
  linarith

lemma dyadic_sqrt_diff (k : ℕ) :
    1 / (4 * Real.sqrt ((2 ^ k : ℕ) : ℝ)) ≤
      1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ) := by
  have ha : 0 < Real.sqrt ((2 ^ k : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hs2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2_ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hsq : (4 / 3 : ℝ) ^ 2 ≤ Real.sqrt 2 ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 2]
  have hpow : Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ) =
      Real.sqrt ((2 ^ k : ℕ) : ℝ) * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    push_cast [pow_succ]
    ring
  rw [hpow]
  have hsub :
      1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / (Real.sqrt ((2 ^ k : ℕ) : ℝ) * Real.sqrt 2) -
        1 / (4 * Real.sqrt ((2 ^ k : ℕ) : ℝ)) =
      (3 * Real.sqrt 2 - 4) / (4 * Real.sqrt ((2 ^ k : ℕ) : ℝ) * Real.sqrt 2) := by
    field_simp
    ring
  have hnn : 0 ≤ (3 * Real.sqrt 2 - 4) / (4 * Real.sqrt ((2 ^ k : ℕ) : ℝ) * Real.sqrt 2) :=
    div_nonneg (by linarith) (by positivity)
  linarith

end OMA.Erdos1191H1

open OMA.Erdos1191H1

theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_i_R1.H1 := by
  intro R S hR hS hAsid
  by_contra hno
  let A : Set ℕ := (S : Set ℕ)
  have hcnt_eq : ∀ n : ℕ, (S.filter (· ≤ n)).card = sidonCount A n := by
    intro n
    unfold sidonCount
    refine Finset.card_bij (fun x _ => x) ?_ (fun _ _ _ _ h => h) ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc, A, Finset.mem_coe] at hx ⊢
      exact ⟨⟨(hS (Finset.mem_coe.mpr hx.1)).1, hx.2⟩, hx.1⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc, A, Finset.mem_coe] at hx ⊢
      exact ⟨x, ⟨hx.2, hx.1.2⟩, rfl⟩
  have hgt_nat : ∀ k ∈ Set.Icc R (2 * R), 512 * 2 ^ k < sidonCount A (2 ^ k) ^ 2 * k := by
    intro k hk
    by_contra hle
    have hle' : (S.filter (· ≤ 2 ^ k)).card ^ 2 * k ≤ 512 * 2 ^ k := by
      rw [hcnt_eq]
      exact Nat.le_of_not_lt hle
    exact hno ⟨k, hk, hle'⟩
  let r : ℕ := 2 ^ R
  have hr1 : 1 ≤ r := Nat.one_le_two_pow
  have hr2 : 2 ≤ r := by
    have : 2 ^ 1 ≤ 2 ^ R := Nat.pow_le_pow_right (by omega) (by omega)
    simpa [r] using this
  have h2r_le_r2 : 2 * r ≤ r ^ 2 := by nlinarith
  have h2r_eq : 2 * r = 2 ^ (R + 1) := by dsimp [r]; rw [pow_succ, mul_comm]
  have hr2_eq : r ^ 2 = 2 ^ (2 * R) := by dsimp [r]; rw [← pow_mul, mul_comm]
  let W : ℕ → Finset ℕ := fun j => (Finset.Ioc j (j + r)).filter (· ∈ A)
  have hsum_swap : (r : ℝ) * ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A),
        (1 / Real.sqrt a) ≤
      ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j := by
    have h1 : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j =
        ∑ j ∈ Finset.Icc r (r ^ 2), ∑ a ∈ W j, (1 / Real.sqrt j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [div_eq_mul_inv]
    rw [h1]
    have h2 : ∑ j ∈ Finset.Icc r (r ^ 2), ∑ a ∈ W j, (1 / Real.sqrt j) ≥
        ∑ j ∈ Finset.Icc r (r ^ 2),
          ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A),
            (if a ∈ W j then 1 / Real.sqrt j else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    rw [Finset.sum_comm] at h2
    refine le_trans ?_ h2
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_Ioc] at ha
    have hsub : Finset.Ico (a - r) a ⊆ (Finset.Icc r (r ^ 2)).filter (fun j => a ∈ W j) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_Icc, W, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ha.2⟩⟩
    calc (r : ℝ) * (1 / Real.sqrt a)
        = ∑ _j ∈ Finset.Ico (a - r) a, (1 / Real.sqrt a) := by
          rw [Finset.sum_const, Nat.card_Ico, show a - (a - r) = r by omega, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.Ico (a - r) a, (1 / Real.sqrt j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          simp only [Finset.mem_Ico] at hj
          have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
          exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hjpos)
            (Real.sqrt_le_sqrt (by exact_mod_cast hj.2.le))
      _ ≤ ∑ j ∈ (Finset.Icc r (r ^ 2)).filter (fun j => a ∈ W j), (1 / Real.sqrt j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ j ∈ Finset.Icc r (r ^ 2), if a ∈ W j then 1 / Real.sqrt j else 0 := by
          rw [Finset.sum_filter]
  have habel_step : (13 / 4 : ℝ) * Real.sqrt (R : ℝ) ≤
      ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A), (1 / Real.sqrt a) := by
    rw [h2r_eq, hr2_eq]
    let B : ℕ → Finset ℕ := fun k => (Finset.Ioc (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ A)
    have hpd : Set.PairwiseDisjoint (Finset.Ioc (R + 1) (2 * R) : Set ℕ) B := by
      intro k₁ hk₁ k₂ hk₂ hne
      change Disjoint (B k₁) (B k₂)
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      simp only [B, Finset.mem_filter, Finset.mem_Ioc] at hx₁ hx₂
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpow : 2 ^ k₁ ≤ 2 ^ (k₂ - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · have hpow : 2 ^ k₂ ≤ 2 ^ (k₁ - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
    have hbiUnion :
        (Finset.Ioc (R + 1) (2 * R)).biUnion B =
          (Finset.Ioc (2 ^ (R + 1)) (2 ^ (2 * R))).filter (· ∈ A) := by
      ext x
      simp only [Finset.mem_biUnion, B, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨k, ⟨hk1, hk2⟩, ⟨hx1, hx2⟩, hxA⟩
        have hlo : 2 ^ (R + 1) ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hhi : 2 ^ k ≤ 2 ^ (2 * R) := Nat.pow_le_pow_right (by omega) hk2
        exact ⟨⟨by omega, by omega⟩, hxA⟩
      · rintro ⟨⟨hx1, hx2⟩, hxA⟩
        have hex : ∃ k, x ≤ 2 ^ k := ⟨2 * R, hx2⟩
        let k := Nat.find hex
        have hk_spec : x ≤ 2 ^ k := Nat.find_spec hex
        have hk_le : k ≤ 2 * R := Nat.find_min' hex hx2
        have hk_gt : R + 1 < k := by
          by_contra hle
          have hpow : 2 ^ k ≤ 2 ^ (R + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hk_prev : 2 ^ (k - 1) < x := by
          have hlt : k - 1 < k := by omega
          have hnot := Nat.find_min hex hlt
          omega
        exact ⟨k, ⟨hk_gt, hk_le⟩, ⟨hk_prev, hk_spec⟩, hxA⟩
    have hdyadic_ge :
        ∑ k ∈ Finset.Ioc (R + 1) (2 * R),
          ((sidonCount A (2 ^ k) : ℝ) - (sidonCount A (2 ^ (k - 1)) : ℝ)) *
            (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) ≤
        ∑ a ∈ (Finset.Ioc (2 ^ (R + 1)) (2 ^ (2 * R))).filter (· ∈ A), (1 / Real.sqrt a) := by
      rw [← hbiUnion, Finset.sum_biUnion hpd]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 : 1 ≤ k := by simp only [Finset.mem_Ioc] at hk; omega
      have hcard_B :
          ((B k).card : ℝ) = (sidonCount A (2 ^ k) : ℝ) - (sidonCount A (2 ^ (k - 1)) : ℝ) := by
        have hpow_le : 2 ^ (k - 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        have hdisj : Disjoint ((Finset.Icc 1 (2 ^ (k - 1))).filter (· ∈ A)) (B k) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [B, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hx1 hx2
          omega
        have hunion :
            (Finset.Icc 1 (2 ^ (k - 1))).filter (· ∈ A) ∪ B k =
              (Finset.Icc 1 (2 ^ k)).filter (· ∈ A) := by
          ext x
          simp only [B, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
          constructor
          · rintro (⟨⟨h1, h2⟩, hxA⟩ | ⟨⟨h1, h2⟩, hxA⟩)
            · exact ⟨⟨h1, h2.trans hpow_le⟩, hxA⟩
            · have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
              exact ⟨⟨by omega, h2⟩, hxA⟩
          · rintro ⟨⟨h1, h2⟩, hxA⟩
            by_cases hle : x ≤ 2 ^ (k - 1)
            · exact Or.inl ⟨⟨h1, hle⟩, hxA⟩
            · exact Or.inr ⟨⟨by omega, h2⟩, hxA⟩
        have h1 : sidonCount A (2 ^ (k - 1)) = ((Finset.Icc 1 (2 ^ (k - 1))).filter (· ∈ A)).card := by
          unfold sidonCount
          refine Finset.card_bij (fun x _ => x) ?_ (fun _ _ _ _ h => h) ?_
          · intro x hx; simpa using hx
          · intro x hx; exact ⟨x, by simpa using hx, rfl⟩
        have h2 : sidonCount A (2 ^ k) = ((Finset.Icc 1 (2 ^ k)).filter (· ∈ A)).card := by
          unfold sidonCount
          refine Finset.card_bij (fun x _ => x) ?_ (fun _ _ _ _ h => h) ?_
          · intro x hx; simpa using hx
          · intro x hx; exact ⟨x, by simpa using hx, rfl⟩
        have hadd : sidonCount A (2 ^ (k - 1)) + (B k).card = sidonCount A (2 ^ k) := by
          rw [h1, h2, ← Finset.card_union_of_disjoint hdisj, hunion]
        have haddR :
            (sidonCount A (2 ^ (k - 1)) : ℝ) + ((B k).card : ℝ) =
              (sidonCount A (2 ^ k) : ℝ) := by
          exact_mod_cast hadd
        linarith
      rw [← hcard_B]
      calc ((B k).card : ℝ) * (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ))
          = ∑ _a ∈ B k, (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ a ∈ B k, (1 / Real.sqrt (a : ℝ)) := by
            refine Finset.sum_le_sum fun a ha => ?_
            simp only [B, Finset.mem_filter, Finset.mem_Ioc] at ha
            have hapos : (0 : ℝ) < a := Nat.cast_pos.mpr (by
              have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
              omega)
            exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hapos)
              (Real.sqrt_le_sqrt (by exact_mod_cast ha.1.2))
    refine le_trans ?_ hdyadic_ge
    rw [abel_sum (fun k => (sidonCount A (2 ^ k) : ℝ))
      (fun k => 1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) (R + 1) (2 * R) (by omega)]
    have htail :
        0 ≤ (sidonCount A (2 ^ (2 * R)) : ℝ) * (1 / Real.sqrt ((2 ^ (2 * R) : ℕ) : ℝ)) := by
      positivity
    have hhead :
        (sidonCount A (2 ^ (R + 1)) : ℝ) * (1 / Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ)) ≤ 2 := by
      have h1 := sidonCount_le_two_sqrt hAsid (Nat.one_le_two_pow : 1 ≤ 2 ^ (R + 1))
      have hspos : 0 < Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      calc (sidonCount A (2 ^ (R + 1)) : ℝ) * (1 / Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ))
          ≤ (2 * Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ)) * (1 / Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 2 := by field_simp
    have hRpos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsR_pos : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.mpr hRpos
    have hmain_sum :
        ((R - 1 : ℕ) : ℝ) * (4 / Real.sqrt (R : ℝ)) ≤
          ∑ k ∈ Finset.Ico (R + 1) (2 * R),
            (sidonCount A (2 ^ k) : ℝ) *
              (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ)) := by
      have hterm : ∀ k ∈ Finset.Ico (R + 1) (2 * R),
          4 / Real.sqrt (R : ℝ) ≤
            (sidonCount A (2 ^ k) : ℝ) *
              (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ)) := by
        intro k hk
        simp only [Finset.mem_Ico] at hk
        have hgt_k := hgt_nat k ⟨by omega, by omega⟩
        have hmul_le : sidonCount A (2 ^ k) ^ 2 * k ≤ sidonCount A (2 ^ k) ^ 2 * (2 * R) :=
          Nat.mul_le_mul_left _ (by omega)
        have hmul_eq : sidonCount A (2 ^ k) ^ 2 * (2 * R) = 2 * (sidonCount A (2 ^ k) ^ 2 * R) := by
          ring
        have h256 : 256 * 2 ^ k ≤ sidonCount A (2 ^ k) ^ 2 * R := by omega
        have h256R :
            256 * ((2 ^ k : ℕ) : ℝ) ≤ (sidonCount A (2 ^ k) : ℝ) ^ 2 * (R : ℝ) := by
          exact_mod_cast h256
        have hcnt_ge :
            16 * Real.sqrt ((2 ^ k : ℕ) : ℝ) / Real.sqrt (R : ℝ) ≤
              (sidonCount A (2 ^ k) : ℝ) := by
          have ha_nn : 0 ≤ 16 * Real.sqrt ((2 ^ k : ℕ) : ℝ) / Real.sqrt (R : ℝ) := by positivity
          have hsq :
              (16 * Real.sqrt ((2 ^ k : ℕ) : ℝ) / Real.sqrt (R : ℝ)) ^ 2 ≤
                (sidonCount A (2 ^ k) : ℝ) ^ 2 := by
            rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hRpos.le,
              div_le_iff₀ hRpos]
            linarith
          nlinarith [ha_nn, Nat.cast_nonneg (α := ℝ) (sidonCount A (2 ^ k))]
        have hdiff := dyadic_sqrt_diff k
        have hmul := mul_le_mul hcnt_ge hdiff (by positivity) (Nat.cast_nonneg _)
        have hsimpl :
            (16 * Real.sqrt ((2 ^ k : ℕ) : ℝ) / Real.sqrt (R : ℝ)) *
              (1 / (4 * Real.sqrt ((2 ^ k : ℕ) : ℝ))) = 4 / Real.sqrt (R : ℝ) := by
          have hs2k : Real.sqrt ((2 ^ k : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
          field_simp
          ring
        linarith
      calc ((R - 1 : ℕ) : ℝ) * (4 / Real.sqrt (R : ℝ))
          = ∑ _k ∈ Finset.Ico (R + 1) (2 * R), (4 / Real.sqrt (R : ℝ)) := by
            rw [Finset.sum_const, Nat.card_Ico, show 2 * R - (R + 1) = R - 1 by omega, nsmul_eq_mul]
        _ ≤ ∑ k ∈ Finset.Ico (R + 1) (2 * R),
              (sidonCount A (2 ^ k) : ℝ) *
                (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ)) :=
            Finset.sum_le_sum hterm
    have hR_arith :
        (13 / 4 : ℝ) * Real.sqrt (R : ℝ) ≤ ((R - 1 : ℕ) : ℝ) * (4 / Real.sqrt (R : ℝ)) - 2 := by
      have hsR_sq : Real.sqrt (R : ℝ) ^ 2 = (R : ℝ) := Real.sq_sqrt hRpos.le
      have hR1 : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ R), Nat.cast_one]
      have hdiff :
          ((R - 1 : ℕ) : ℝ) * (4 / Real.sqrt (R : ℝ)) - 2 - (13 / 4) * Real.sqrt (R : ℝ) =
            (3 * (R : ℝ) - 16 - 8 * Real.sqrt (R : ℝ)) / (4 * Real.sqrt (R : ℝ)) := by
        rw [hR1]
        field_simp
        nlinarith [hsR_sq]
      have hR16 : (16 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      have hnum : 0 ≤ 3 * (R : ℝ) - 16 - 8 * Real.sqrt (R : ℝ) := by
        nlinarith [sq_nonneg (Real.sqrt (R : ℝ) - 4), hsR_sq, hR16]
      have hnn :
          0 ≤ (3 * (R : ℝ) - 16 - 8 * Real.sqrt (R : ℝ)) / (4 * Real.sqrt (R : ℝ)) :=
        div_nonneg hnum (by positivity)
      linarith
    linarith
  have hL : (13 / 4 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ) ≤
      ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j := by
    calc (13 / 4 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ)
        = (r : ℝ) * ((13 / 4 : ℝ) * Real.sqrt (R : ℝ)) := by ring
      _ ≤ (r : ℝ) * ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A), (1 / Real.sqrt a) :=
          mul_le_mul_of_nonneg_left habel_step (Nat.cast_nonneg r)
      _ ≤ ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j := hsum_swap
  have hCS : (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j) ^ 2 ≤
      (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2) *
        (∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ))) := by
    have hraw := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc r (r ^ 2))
      (fun j => ((W j).card : ℝ)) (fun j => 1 / Real.sqrt j)
    have hlhs : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) * (1 / Real.sqrt j) =
        ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j :=
      Finset.sum_congr rfl fun j _ => by ring
    have hrhs : ∑ j ∈ Finset.Icc r (r ^ 2), (1 / Real.sqrt j) ^ 2 =
        ∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg j)]
    rw [hlhs, hrhs] at hraw
    exact hraw
  have hsum_sq : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2 ≤ 5 * (r : ℝ) ^ 2 := by
    have hsub : Finset.Icc r (r ^ 2) ⊆ Finset.Icc 1 (r ^ 2) :=
      Finset.Icc_subset_Icc hr1 le_rfl
    have h1 : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2 ≤
        ∑ j ∈ Finset.Icc 1 (r ^ 2), ((W j).card : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    have h2 : ∑ j ∈ Finset.Icc 1 (r ^ 2), ((W j).card : ℝ) ^ 2 ≤ 5 * (r : ℝ) ^ 2 := by
      exact_mod_cast sidon_window_sq_sum_le hAsid hr1
    exact h1.trans h2
  have hsum_harm : ∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ)) ≤ 2 * Real.log (r : ℝ) := by
    have h1 := harmonic_Icc_le_log hr2 (Nat.le_self_pow (by norm_num : 2 ≠ 0) r)
    push_cast at h1
    rw [Real.log_pow, Nat.cast_ofNat] at h1
    exact h1
  have hLHS_sq : (169 / 16 : ℝ) * (r : ℝ) ^ 2 * (R : ℝ) ≤
      (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j) ^ 2 := by
    have h1 : ((13 / 4 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ)) ^ 2 ≤
        (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hL 2
    have h2 : ((13 / 4 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ)) ^ 2 =
        (169 / 16 : ℝ) * (r : ℝ) ^ 2 * (R : ℝ) := by
      have hsR : Real.sqrt (R : ℝ) ^ 2 = (R : ℝ) := Real.sq_sqrt (Nat.cast_nonneg R)
      calc ((13 / 4 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ)) ^ 2
          = (169 / 16 : ℝ) * (r : ℝ) ^ 2 * Real.sqrt (R : ℝ) ^ 2 := by ring
        _ = (169 / 16 : ℝ) * (r : ℝ) ^ 2 * (R : ℝ) := by rw [hsR]
    linarith
  have hRHS_le : (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2) *
        (∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ))) ≤
      10 * (r : ℝ) ^ 2 * Real.log (r : ℝ) := by
    calc (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2) *
          (∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ)))
        ≤ (5 * (r : ℝ) ^ 2) * (2 * Real.log (r : ℝ)) :=
          mul_le_mul hsum_sq hsum_harm
            (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = 10 * (r : ℝ) ^ 2 * Real.log (r : ℝ) := by ring
  have hlogr : Real.log (r : ℝ) ≤ (R : ℝ) := by
    have hrcast : (r : ℝ) = (2 : ℝ) ^ R := by dsimp [r]; push_cast; rfl
    rw [hrcast, Real.log_pow]
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmul := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (α := ℝ) R)
    linarith
  have h10 : 10 * (r : ℝ) ^ 2 * Real.log (r : ℝ) ≤ 10 * (r : ℝ) ^ 2 * (R : ℝ) :=
    mul_le_mul_of_nonneg_left hlogr (by positivity)
  have hr2R_pos : 0 < (r : ℝ) ^ 2 * (R : ℝ) := by
    have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr1
    have hR_pos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
    positivity
  have hfinal : (169 / 16 : ℝ) * (r : ℝ) ^ 2 * (R : ℝ) ≤ 10 * (r : ℝ) ^ 2 * (R : ℝ) :=
    hLHS_sq.trans (hCS.trans (hRHS_le.trans h10))
  have hlt : 10 * (r : ℝ) ^ 2 * (R : ℝ) < (169 / 16 : ℝ) * (r : ℝ) ^ 2 * (R : ℝ) := by
    have h1 : 10 * ((r : ℝ) ^ 2 * (R : ℝ)) < (169 / 16 : ℝ) * ((r : ℝ) ^ 2 * (R : ℝ)) :=
      mul_lt_mul_of_pos_right (by norm_num) hr2R_pos
    rw [← mul_assoc, ← mul_assoc] at h1
    exact h1
  exact not_le_of_gt hlt hfinal
