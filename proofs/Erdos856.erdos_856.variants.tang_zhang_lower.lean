import FormalConjectures.ErdosProblems.«856»

/-!
# Proof of Erdős Problem 856 — Tang–Zhang lower bound

We prove `Erdos856.erdos_856.variants.tang_zhang_lower`: for fixed `k ≥ 3` and `ε > 0`,
eventually `Real.log N ^ (tangZhangExponent k - ε) ≤ f k N`, where
`tangZhangExponent k = (k - 2) / (e * ((k - 2)!)^(1 / (k - 2)))`.

The proof is completely elementary and self-contained:
1. Euler product lower bound `log (log X) - 1 ≤ ∑_{p ≤ X} 1/p` for all `X ≥ 3`.
2. Greedy partitioning of primes in `[P₀, X]` into `R` disjoint blocks `P_0, ..., P_{R-1}`,
   each of harmonic sum `≥ x := e * (d!)^(1/d)` (`d = k - 2`).
3. Elementary symmetric polynomial lower bound `e_d(P_r) ≥ (x - d * δ)^d / d!`.
4. Constructing `A` as all products of `d` distinct primes from each block `P_r` (`0 ≤ r < R`):
   `A ⊆ Icc 1 N`, `A` has no `k`-tuple with equal pairwise LCM (by a 1-block co-sunflower
   contradiction `k - 1 ≤ k - 2`), and `∑_{n ∈ A} 1/n ≥ ((x - d * δ)^d / d!)^R ≥ (log N)^(c_k - ε)`.
-/

-- Problem: Erdős Problem 856 — tang zhang lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/856.lean:114 (declaration Erdos856.erdos_856.variants.tang_zhang_lower)
-- Credit: @Dugongue (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Finset BigOperators

namespace Erdos856TangZhang

/- ### Section 1: Elementary Euler product lower bound on `∑_{p ≤ X} 1 / p` -/

private lemma log_le_harmonic (X : ℕ) :
    Real.log ((X + 1 : ℕ) : ℝ) ≤ ∑ n ∈ Finset.Icc 1 X, ((n : ℝ)⁻¹) := by
  induction X with
  | zero => simp
  | succ X ih =>
    have hsplit : Finset.Icc 1 (X + 1) = insert (X + 1) (Finset.Icc 1 X) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : X + 1 ∉ Finset.Icc 1 X := by simp
    rw [hsplit, Finset.sum_insert hnotmem]
    have hpos1 : (0 : ℝ) < (X + 1 : ℕ) := by positivity
    have hpos2 : (0 : ℝ) < (X + 2 : ℕ) := by positivity
    have hstep : Real.log ((X + 2 : ℕ) : ℝ) - Real.log ((X + 1 : ℕ) : ℝ) ≤ ((X + 1 : ℕ) : ℝ)⁻¹ := by
      rw [← Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos1)]
      calc Real.log (((X + 2 : ℕ) : ℝ) / ((X + 1 : ℕ) : ℝ))
          ≤ ((X + 2 : ℕ) : ℝ) / ((X + 1 : ℕ) : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hpos2 hpos1)
        _ = ((X + 1 : ℕ) : ℝ)⁻¹ := by
            push_cast
            field_simp
            ring
    linarith

private lemma telescoping_inv_mul_pred (X : ℕ) :
    ∑ n ∈ Finset.Icc 2 X, ((n : ℝ) * ((n : ℝ) - 1))⁻¹ ≤ 1 := by
  have hsum : ∀ m : ℕ, ∑ n ∈ Finset.Icc 2 (m + 1), ((n : ℝ) * ((n : ℝ) - 1))⁻¹ =
      1 - ((m + 1 : ℕ) : ℝ)⁻¹ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsplit : Finset.Icc 2 (m + 2) = insert (m + 2) (Finset.Icc 2 (m + 1)) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnm : m + 2 ∉ Finset.Icc 2 (m + 1) := by simp
      rw [hsplit, Finset.sum_insert hnm, ih]
      have h1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (m : ℝ) + 2 ≠ 0 := by positivity
      have hpart : (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 1))⁻¹ =
          ((m + 1 : ℕ) : ℝ)⁻¹ - ((m + 2 : ℕ) : ℝ)⁻¹ := by
        push_cast
        have hsub : (m : ℝ) + 2 - 1 = (m : ℝ) + 1 := by ring
        rw [hsub]
        field_simp
        ring
      linarith
  cases X with
  | zero => simp
  | succ m =>
    rw [hsum m]
    have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ)⁻¹ := by positivity
    linarith

private lemma sum_smooth_le_euler_prod (Q : Finset ℕ) (hQ : ∀ p ∈ Q, Nat.Prime p) (X : ℕ) :
    ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ∀ q ∈ n.primeFactors, q ∈ Q), ((n : ℝ)⁻¹) ≤
      ∏ p ∈ Q, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  induction Q using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    have hsub : (Finset.Icc 1 X).filter (fun n => ∀ q ∈ n.primeFactors, q ∈ (∅ : Finset ℕ)) ⊆ {1} := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton] at hn ⊢
      by_contra hne1
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne1
      have hqmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqdvd, by omega⟩
      exact Finset.notMem_empty q (hn.2 q hqmem)
    calc ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ∀ q ∈ n.primeFactors, q ∈ (∅ : Finset ℕ)), ((n : ℝ)⁻¹)
        ≤ ∑ n ∈ ({1} : Finset ℕ), ((n : ℝ)⁻¹) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | insert p Q' hpQ ih =>
    have hp : Nat.Prime p := hQ p (Finset.mem_insert_self p Q')
    have hQ' : ∀ q ∈ Q', Nat.Prime q := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hpQ]
    let S1 := (Finset.Icc 1 X).filter (fun n => ∀ q ∈ n.primeFactors, q ∈ insert p Q')
    let S0 := (Finset.Icc 1 X).filter (fun m => ∀ q ∈ m.primeFactors, q ∈ Q')
    -- Bound geometric sum for p by (1 - 1/p)⁻¹
    have hgeom_p : ∑ e ∈ Finset.range (X + 1), ((p : ℝ)⁻¹) ^ e ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hlt1 : (p : ℝ)⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
      rw [geom_sum_eq (ne_of_lt hlt1)]
      have hden : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
      rw [div_eq_mul_inv,
        show (p : ℝ)⁻¹ ^ (X + 1) - 1 = -(1 - (p : ℝ)⁻¹ ^ (X + 1)) by ring,
        show (p : ℝ)⁻¹ - 1 = -(1 - (p : ℝ)⁻¹) by ring,
        inv_neg, neg_mul_neg]
      have hpow : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ (X + 1) := by positivity
      nlinarith [inv_nonneg.mpr (le_of_lt hden)]
    -- Embed S1 into (range (X+1)) ×ˢ S0 via n ↦ (n.factorization p, n / p ^ (n.factorization p))
    let split : ℕ → ℕ × ℕ := fun n => (n.factorization p, n / p ^ (n.factorization p))
    have hsplit_mul : ∀ n ∈ S1, p ^ (split n).1 * (split n).2 = n := by
      intro n _
      exact Nat.mul_div_cancel' (Nat.ordProj_dvd n p)
    have hsplit_mem : ∀ n ∈ S1, split n ∈ Finset.range (X + 1) ×ˢ S0 := by
      intro n hn
      simp only [S1, Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_product, Finset.mem_range]
      dsimp only [split]
      have hdvd : p ^ (n.factorization p) ∣ n := Nat.ordProj_dvd n p
      have hle : p ^ (n.factorization p) ≤ n := Nat.le_of_dvd (by omega) hdvd
      have h2le : 2 ^ (n.factorization p) ≤ p ^ (n.factorization p) := Nat.pow_le_pow_left hp.two_le _
      have hlt : n.factorization p < 2 ^ (n.factorization p) := Nat.lt_two_pow_self
      refine ⟨by omega, ?_⟩
      simp only [S0, Finset.mem_filter, Finset.mem_Icc]
      have hmpos : 1 ≤ n / p ^ (n.factorization p) := Nat.div_pos hle (pow_pos hp.pos _)
      have hmle : n / p ^ (n.factorization p) ≤ X := le_trans (Nat.div_le_self n _) hn.1.2
      refine ⟨⟨hmpos, hmle⟩, fun q hq => ?_⟩
      rw [Nat.mem_primeFactors] at hq
      have hq_dvd_n : q ∣ n := dvd_trans hq.2.1 (Nat.div_dvd_of_dvd hdvd)
      have hq_in : q ∈ insert p Q' := hn.2 q (Nat.mem_primeFactors.mpr ⟨hq.1, hq_dvd_n, by omega⟩)
      rw [Finset.mem_insert] at hq_in
      rcases hq_in with rfl | hq'
      · exfalso
        exact Nat.not_dvd_ordCompl hp (by omega : n ≠ 0) hq.2.1
      · exact hq'
    have hsplit_inj : Set.InjOn split (S1 : Set ℕ) := by
      intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      rw [← hsplit_mul a ha, ← hsplit_mul b hb, hab]
    have hsplit_val : ∀ n ∈ S1, ((p : ℝ)⁻¹) ^ (split n).1 * ((split n).2 : ℝ)⁻¹ = (n : ℝ)⁻¹ := by
      intro n hn
      rw [inv_pow, ← Nat.cast_pow, ← mul_inv, ← Nat.cast_mul, hsplit_mul n hn]
    have hstep1 : ∑ n ∈ S1, ((n : ℝ)⁻¹) ≤
        (∑ e ∈ Finset.range (X + 1), ((p : ℝ)⁻¹) ^ e) * (∑ m ∈ S0, ((m : ℝ)⁻¹)) := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      calc ∑ n ∈ S1, ((n : ℝ)⁻¹)
          = ∑ n ∈ S1, ((p : ℝ)⁻¹) ^ (split n).1 * ((split n).2 : ℝ)⁻¹ :=
            Finset.sum_congr rfl fun n hn => (hsplit_val n hn).symm
        _ = ∑ z ∈ S1.image split, ((p : ℝ)⁻¹) ^ z.1 * (z.2 : ℝ)⁻¹ :=
            (Finset.sum_image (f := fun z : ℕ × ℕ => ((p : ℝ)⁻¹) ^ z.1 * (z.2 : ℝ)⁻¹)
              (fun a ha b hb h => hsplit_inj ha hb h)).symm
        _ ≤ ∑ z ∈ Finset.range (X + 1) ×ˢ S0, ((p : ℝ)⁻¹) ^ z.1 * (z.2 : ℝ)⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro z hz
            rw [Finset.mem_image] at hz
            obtain ⟨n, hn, rfl⟩ := hz
            exact hsplit_mem n hn
    have hS0_le : ∑ m ∈ S0, ((m : ℝ)⁻¹) ≤ ∏ q ∈ Q', (1 - (q : ℝ)⁻¹)⁻¹ := ih hQ'
    have hS0_nn : 0 ≤ ∑ m ∈ S0, ((m : ℝ)⁻¹) := Finset.sum_nonneg (fun _ _ => by positivity)
    have hgeom_nn : 0 ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have : (p : ℝ)⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
      exact inv_nonneg.mpr (by linarith)
    exact le_trans hstep1 (mul_le_mul hgeom_p hS0_le hS0_nn hgeom_nn)

private lemma harmonic_le_euler_prod (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, ((n : ℝ)⁻¹) ≤
      ∏ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ := by
  let P := (Finset.Icc 1 X).filter Nat.Prime
  have heq : (Finset.Icc 1 X).filter (fun n => ∀ q ∈ n.primeFactors, q ∈ P) = Finset.Icc 1 X := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc, and_iff_left_iff_imp]
    intro hn q hq
    rw [Nat.mem_primeFactors] at hq
    simp only [P, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hq.1.pos, le_trans (Nat.le_of_dvd (by omega) hq.2.1) hn.2⟩, hq.1⟩
  conv_lhs => rw [← heq]
  exact sum_smooth_le_euler_prod P (fun p hp => (Finset.mem_filter.mp hp).2) X

private lemma prime_harmonic_lower_bound {X : ℕ} (hX : 3 ≤ X) :
    Real.log (Real.log (X : ℝ)) - 1 ≤
      ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  let P := (Finset.Icc 1 X).filter Nat.Prime
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    apply Real.log_pos; exact_mod_cast (by omega : 1 < X)
  have h1 : Real.log (X : ℝ) ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ := by
    calc Real.log (X : ℝ)
        ≤ Real.log ((X + 1 : ℕ) : ℝ) := Real.log_le_log hXpos (by exact_mod_cast (by omega : X ≤ X + 1))
      _ ≤ ∑ n ∈ Finset.Icc 1 X, ((n : ℝ)⁻¹) := log_le_harmonic X
      _ ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ := harmonic_le_euler_prod X
  have hprod_ne : ∀ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ ≠ 0 := by
    intro p hp
    have hpr : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have : (p : ℝ)⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
    exact inv_ne_zero (by linarith)
  have hlog1 : Real.log (Real.log (X : ℝ)) ≤ ∑ p ∈ P, Real.log ((1 - (p : ℝ)⁻¹)⁻¹) := by
    calc Real.log (Real.log (X : ℝ))
        ≤ Real.log (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) := Real.log_le_log hlog_pos h1
      _ = ∑ p ∈ P, Real.log ((1 - (p : ℝ)⁻¹)⁻¹) := Real.log_prod hprod_ne
  have hterm : ∀ p ∈ P, Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤ (p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    intro p hp
    have hpr : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have hlt1 : (p : ℝ)⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
    have hpos : (0 : ℝ) < (1 - (p : ℝ)⁻¹)⁻¹ := inv_pos.mpr (by linarith)
    calc Real.log ((1 - (p : ℝ)⁻¹)⁻¹)
        ≤ (1 - (p : ℝ)⁻¹)⁻¹ - 1 := Real.log_le_sub_one_of_pos hpos
      _ = (p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          have h1p : 1 - (p : ℝ)⁻¹ ≠ 0 := by linarith
          field_simp
          ring
  have hsub : P ⊆ Finset.Icc 2 X := by
    intro p hp
    simp only [P, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨hp.2.two_le, hp.1.2⟩
  have htail : ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ ≤ 1 := by
    calc ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹
        ≤ ∑ n ∈ Finset.Icc 2 X, ((n : ℝ) * ((n : ℝ) - 1))⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => ?_
          have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
          exact inv_nonneg.mpr this
      _ ≤ 1 := telescoping_inv_mul_pred X
  have hsum2 : ∑ p ∈ P, Real.log ((1 - (p : ℝ)⁻¹)⁻¹) ≤
      (∑ p ∈ P, (p : ℝ)⁻¹) + ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hterm
  linarith

/- ### Section 2: Greedy chunking into disjoint prime blocks -/

private lemma exists_minimal_chunk {S : Finset ℕ} {f : ℕ → ℝ} {x δ : ℝ}
    (hnn : ∀ p ∈ S, 0 ≤ f p) (hδ : ∀ p ∈ S, f p ≤ δ) (hx : 0 ≤ x) (hδ0 : 0 ≤ δ)
    (hsum : x ≤ ∑ p ∈ S, f p) :
    ∃ P ⊆ S, x ≤ ∑ p ∈ P, f p ∧ ∑ p ∈ P, f p ≤ x + δ := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp at hsum
    refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩ <;> simp <;> linarith
  | insert a s ha ih =>
    have hnn_s : ∀ p ∈ s, 0 ≤ f p := fun p hp => hnn p (Finset.mem_insert_of_mem hp)
    have hδ_s : ∀ p ∈ s, f p ≤ δ := fun p hp => hδ p (Finset.mem_insert_of_mem hp)
    by_cases hs : x ≤ ∑ p ∈ s, f p
    · obtain ⟨P, hPs, hP1, hP2⟩ := ih hnn_s hδ_s hs
      exact ⟨P, Finset.Subset.trans hPs (Finset.subset_insert a s), hP1, hP2⟩
    · refine ⟨insert a s, Finset.Subset.refl _, hsum, ?_⟩
      rw [Finset.sum_insert ha]
      have hfa : f a ≤ δ := hδ a (Finset.mem_insert_self a s)
      linarith

private lemma exists_disjoint_chunks (R : ℕ) {S : Finset ℕ} {f : ℕ → ℝ} {x δ : ℝ}
    (hnn : ∀ p ∈ S, 0 ≤ f p) (hδ : ∀ p ∈ S, f p ≤ δ) (hx : 0 ≤ x) (hδ0 : 0 ≤ δ)
    (hsum : (R : ℝ) * (x + δ) ≤ ∑ p ∈ S, f p) :
    ∃ P : Fin R → Finset ℕ,
      (∀ r, P r ⊆ S) ∧
      (∀ r1 r2, r1 ≠ r2 → Disjoint (P r1) (P r2)) ∧
      (∀ r, x ≤ ∑ p ∈ P r, f p) := by
  classical
  induction R generalizing S with
  | zero =>
    exact ⟨Fin.elim0, fun r => r.elim0, fun r => r.elim0, fun r => r.elim0⟩
  | succ R ih =>
    have hxle : x ≤ ∑ p ∈ S, f p := by
      have h1 : (1 : ℝ) ≤ (R + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ R + 1)
      have h2 : x ≤ 1 * (x + δ) := by linarith
      have h3 : 1 * (x + δ) ≤ ((R + 1 : ℕ) : ℝ) * (x + δ) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      linarith
    obtain ⟨P0, hP0S, hP0_lo, hP0_hi⟩ := exists_minimal_chunk hnn hδ hx hδ0 hxle
    let S' := S \ P0
    have hsum' : (R : ℝ) * (x + δ) ≤ ∑ p ∈ S', f p := by
      have hpart : ∑ p ∈ S', f p + ∑ p ∈ P0, f p = ∑ p ∈ S, f p :=
        Finset.sum_sdiff hP0S
      push_cast at hsum
      linarith
    obtain ⟨P', hP'sub, hP'disj, hP'lo⟩ := ih
      (fun p hp => hnn p (Finset.mem_sdiff.mp hp).1)
      (fun p hp => hδ p (Finset.mem_sdiff.mp hp).1)
      hsum'
    refine ⟨Fin.cons P0 P', ?_, ?_, ?_⟩
    · intro r
      refine Fin.cases hP0S (fun i => Finset.Subset.trans (hP'sub i) Finset.sdiff_subset) r
    · intro r1 r2
      refine Fin.cases ?_ (fun i => ?_) r1
      · refine Fin.cases (fun h => False.elim (h rfl)) (fun j _ => ?_) r2
        rw [Finset.disjoint_left]; intro p hp0 hpj
        exact (Finset.mem_sdiff.mp (hP'sub j hpj)).2 hp0
      · refine Fin.cases (fun _ => ?_) (fun j h => ?_) r2
        · rw [Finset.disjoint_left]; intro p hpi hp0
          exact (Finset.mem_sdiff.mp (hP'sub i hpi)).2 hp0
        · exact hP'disj i j (fun hij => h (congrArg Fin.succ hij))
    · intro r
      exact Fin.cases hP0_lo hP'lo r

/- ### Section 3: Elementary symmetric polynomial lower bound -/

private lemma elemSym_step (P : Finset ℕ) (f : ℕ → ℝ) (d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * ∑ T ∈ P.powersetCard (d + 1), ∏ p ∈ T, f p =
      ∑ S ∈ P.powersetCard d, (∏ q ∈ S, f q) * (∑ p ∈ P \ S, f p) := by
  classical
  -- Double count pairs (S, p) with S ∈ powersetCard d, p ∈ P \ S vs (T, p) with T ∈ powersetCard (d+1), p ∈ T
  have h1 : ∑ S ∈ P.powersetCard d, (∏ q ∈ S, f q) * (∑ p ∈ P \ S, f p) =
      ∑ x ∈ (P.powersetCard d).sigma (fun S => P \ S), (∏ q ∈ x.1, f q) * f x.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum]
  have h2 : ((d + 1 : ℕ) : ℝ) * ∑ T ∈ P.powersetCard (d + 1), ∏ p ∈ T, f p =
      ∑ y ∈ (P.powersetCard (d + 1)).sigma (fun T => T), ∏ p ∈ y.1, f p := by
    rw [Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    dsimp only
    rw [Finset.sum_const, (Finset.mem_powersetCard.mp hT).2, nsmul_eq_mul]
  rw [h1, h2]
  refine Finset.sum_bij (fun y _ => ⟨y.1.erase y.2, y.2⟩) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hy ⊢
    refine ⟨⟨Finset.Subset.trans (Finset.erase_subset y.2 y.1) hy.1.1, ?_⟩,
            hy.1.1 hy.2, Finset.notMem_erase y.2 y.1⟩
    rw [Finset.card_erase_of_mem hy.2, hy.1.2]; omega
  · intro y1 hy1 y2 hy2 heq
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
    obtain ⟨herase, h2eq⟩ := heq
    simp only [Finset.mem_sigma] at hy1 hy2
    have h1eq : y1.1 = y2.1 := by
      rw [← Finset.insert_erase hy1.2, ← Finset.insert_erase hy2.2, herase, h2eq]
    exact Sigma.ext h1eq (by rw [h2eq])
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hx
    refine ⟨⟨insert x.2 x.1, x.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_powersetCard]
      refine ⟨⟨Finset.insert_subset hx.2.1 hx.1.1, ?_⟩, Finset.mem_insert_self x.2 x.1⟩
      rw [Finset.card_insert_of_notMem hx.2.2, hx.1.2]
    · exact Sigma.ext (Finset.erase_insert hx.2.2) (by rfl)
  · intro y hy
    simp only [Finset.mem_sigma] at hy
    rw [mul_comm, Finset.mul_prod_erase y.1 f hy.2]

private lemma elemSym_lower_bound (P : Finset ℕ) (f : ℕ → ℝ) (δ : ℝ)
    (hnn : ∀ p ∈ P, 0 ≤ f p) (hδ : ∀ p ∈ P, f p ≤ δ) (hδ0 : 0 ≤ δ) :
    ∀ d : ℕ, (d : ℝ) * δ ≤ ∑ p ∈ P, f p →
      (∑ p ∈ P, f p - (d : ℝ) * δ) ^ d / (d.factorial : ℝ) ≤
        ∑ S ∈ P.powersetCard d, ∏ p ∈ S, f p := by
  intro d
  induction d with
  | zero =>
    intro _
    simp
  | succ d ih =>
    intro hW
    set W := ∑ p ∈ P, f p
    have hWd : (d : ℝ) * δ ≤ W := by
      push_cast at hW; nlinarith
    have hih := ih hWd
    have hstep := elemSym_step P f d
    have hrem : ∀ S ∈ P.powersetCard d, W - (d : ℝ) * δ ≤ ∑ p ∈ P \ S, f p := by
      intro S hS
      obtain ⟨hSP, hScard⟩ := Finset.mem_powersetCard.mp hS
      have hpart : ∑ p ∈ P \ S, f p + ∑ p ∈ S, f p = W := Finset.sum_sdiff hSP
      have hS_ub : ∑ p ∈ S, f p ≤ (d : ℝ) * δ := by
        calc ∑ p ∈ S, f p ≤ ∑ _p ∈ S, δ := Finset.sum_le_sum fun p hp => hδ p (hSP hp)
          _ = (S.card : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = (d : ℝ) * δ := by rw [hScard]
      linarith
    have hge1 : (∑ S ∈ P.powersetCard d, ∏ q ∈ S, f q) * (W - (d : ℝ) * δ) ≤
        ((d + 1 : ℕ) : ℝ) * ∑ T ∈ P.powersetCard (d + 1), ∏ p ∈ T, f p := by
      rw [hstep, Finset.sum_mul]
      refine Finset.sum_le_sum fun S hS => ?_
      have hprod_nn : 0 ≤ ∏ q ∈ S, f q :=
        Finset.prod_nonneg fun q hq => hnn q ((Finset.mem_powersetCard.mp hS).1 hq)
      exact mul_le_mul_of_nonneg_left (hrem S hS) hprod_nn
    have hbase_le : W - ((d + 1 : ℕ) : ℝ) * δ ≤ W - (d : ℝ) * δ := by
      push_cast; linarith
    have hbase_nn : 0 ≤ W - ((d + 1 : ℕ) : ℝ) * δ := by linarith
    have hpow_le : (W - ((d + 1 : ℕ) : ℝ) * δ) ^ d ≤ (W - (d : ℝ) * δ) ^ d :=
      pow_le_pow_left₀ hbase_nn hbase_le d
    have hfac_pos : (0 : ℝ) < (d.factorial : ℝ) := by positivity
    have hd1_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((d + 1).factorial : ℝ))]
    rw [Nat.factorial_succ, Nat.cast_mul]
    have h1 : (W - ((d + 1 : ℕ) : ℝ) * δ) ^ (d + 1) ≤
        ((W - (d : ℝ) * δ) ^ d / (d.factorial : ℝ)) * (W - (d : ℝ) * δ) * (d.factorial : ℝ) := by
      have hmul : (W - ((d + 1 : ℕ) : ℝ) * δ) ^ d * (W - ((d + 1 : ℕ) : ℝ) * δ) ≤
          (W - (d : ℝ) * δ) ^ d * (W - (d : ℝ) * δ) :=
        mul_le_mul hpow_le hbase_le hbase_nn (pow_nonneg (by linarith) d)
      rw [pow_succ]
      have hcancel : (W - (d : ℝ) * δ) ^ d / (d.factorial : ℝ) * (W - (d : ℝ) * δ) * (d.factorial : ℝ) =
          (W - (d : ℝ) * δ) ^ d * (W - (d : ℝ) * δ) := by field_simp
      linarith
    have h2 : ((W - (d : ℝ) * δ) ^ d / (d.factorial : ℝ)) * (W - (d : ℝ) * δ) ≤
        (∑ S ∈ P.powersetCard d, ∏ q ∈ S, f q) * (W - (d : ℝ) * δ) :=
      mul_le_mul_of_nonneg_right hih (by linarith)
    nlinarith

/- ### Section 4: Block-product construction & co-sunflower exclusion -/

private lemma primeFactors_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    (∏ p ∈ S, p).primeFactors = S := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hap : Nat.Prime a := hS a (Finset.mem_insert_self a s)
    have hsp : ∀ p ∈ s, Nat.Prime p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hprod_ne : ∏ p ∈ s, p ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; exact fun p hp => (hsp p hp).ne_zero
    rw [Finset.prod_insert ha, Nat.primeFactors_mul hap.ne_zero hprod_ne,
      hap.primeFactors, ih hsp]
    ext q; simp

private lemma prod_primes_inj {S1 S2 : Finset ℕ}
    (h1 : ∀ p ∈ S1, Nat.Prime p) (h2 : ∀ p ∈ S2, Nat.Prime p)
    (heq : ∏ p ∈ S1, p = ∏ p ∈ S2, p) : S1 = S2 := by
  rw [← primeFactors_prod_primes h1, ← primeFactors_prod_primes h2, heq]

private lemma primeFactors_lcm_eq_union {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_union, Nat.lcm_ne_zero ha hb, ne_eq,
    not_false_eq_true, and_true]
  constructor
  · rintro ⟨hp, hdvd⟩
    have hmul : p ∣ a * b := dvd_trans hdvd (Nat.lcm_dvd_mul a b)
    rcases hp.dvd_mul.mp hmul with h | h
    · left; exact ⟨hp, h, ha⟩
    · right; exact ⟨hp, h, hb⟩
  · rintro (⟨hp, h, _⟩ | ⟨hp, h, _⟩)
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left a b)⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right a b)⟩

private lemma block_product_construction {k R X N : ℕ} (hk : 3 ≤ k)
    (P : Fin R → Finset ℕ)
    (hP_prime : ∀ r, ∀ p ∈ P r, Nat.Prime p)
    (hP_le : ∀ r, ∀ p ∈ P r, p ≤ X)
    (hP_disj : ∀ r1 r2, r1 ≠ r2 → Disjoint (P r1) (P r2))
    (hXN : X ^ (R * (k - 2)) ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ ¬ Erdos856.HasEqualLcmTuple k A ∧
      ∑ n ∈ A, (n : ℝ)⁻¹ = ∏ r : Fin R, ∑ S ∈ (P r).powersetCard (k - 2), ∏ p ∈ S, (p : ℝ)⁻¹ := by
  classical
  set d := k - 2
  let Ω : Finset (Fin R → Finset ℕ) := Fintype.piFinset (fun r => (P r).powersetCard d)
  let Φ : (Fin R → Finset ℕ) → ℕ := fun g => ∏ r : Fin R, ∏ p ∈ g r, p
  let A : Finset ℕ := Ω.image Φ
  -- For any g ∈ Ω, Φ g is a product of distinct primes (their union over r)
  have hΦ_pf : ∀ g ∈ Ω, (Φ g).primeFactors = Finset.univ.biUnion g := by
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    have hdisj_g : ∀ r1 r2 : Fin R, r1 ≠ r2 → Disjoint (g r1) (g r2) := by
      intro r1 r2 hne
      exact (hP_disj r1 r2 hne).mono (Finset.mem_powersetCard.mp (hg r1)).1
        (Finset.mem_powersetCard.mp (hg r2)).1
    have hΦ_eq : Φ g = ∏ p ∈ Finset.univ.biUnion g, p := by
      unfold Φ
      symm
      exact Finset.prod_biUnion (fun r1 _ r2 _ hne => hdisj_g r1 r2 hne)
    rw [hΦ_eq]
    refine primeFactors_prod_primes fun p hp => ?_
    rw [Finset.mem_biUnion] at hp
    obtain ⟨r, _, hpr⟩ := hp
    exact hP_prime r p ((Finset.mem_powersetCard.mp (hg r)).1 hpr)
  have hΦ_inter : ∀ g ∈ Ω, ∀ r : Fin R, (Φ g).primeFactors ∩ P r = g r := by
    intro g hg r
    rw [hΦ_pf g hg]
    rw [Fintype.mem_piFinset] at hg
    ext p
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨r', hpr'⟩, hpr⟩
      by_cases hrr : r' = r
      · rwa [← hrr]
      · exfalso
        have h1 : p ∈ P r' := (Finset.mem_powersetCard.mp (hg r')).1 hpr'
        exact Finset.disjoint_left.mp (hP_disj r' r hrr) h1 hpr
    · intro hpr
      exact ⟨⟨r, hpr⟩, (Finset.mem_powersetCard.mp (hg r)).1 hpr⟩
  have hΦ_inj : Set.InjOn Φ (Ω : Set (Fin R → Finset ℕ)) := by
    intro g1 hg1 g2 hg2 heq
    rw [Finset.mem_coe] at hg1 hg2
    funext r
    rw [← hΦ_inter g1 hg1 r, ← hΦ_inter g2 hg2 r, heq]
  have hΦ_pos : ∀ g ∈ Ω, 1 ≤ Φ g := by
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    unfold Φ
    refine Finset.one_le_prod' fun r _ => Finset.one_le_prod' fun p hp => ?_
    exact (hP_prime r p ((Finset.mem_powersetCard.mp (hg r)).1 hp)).pos
  have hΦ_le : ∀ g ∈ Ω, Φ g ≤ N := by
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    calc Φ g = ∏ r : Fin R, ∏ p ∈ g r, p := rfl
      _ ≤ ∏ r : Fin R, ∏ _p ∈ g r, X := by
          refine Finset.prod_le_prod' fun r _ => Finset.prod_le_prod' fun p hp => ?_
          exact hP_le r p ((Finset.mem_powersetCard.mp (hg r)).1 hp)
      _ = ∏ _r : Fin R, X ^ d := by
          refine Finset.prod_congr rfl fun r _ => ?_
          rw [Finset.prod_const, (Finset.mem_powersetCard.mp (hg r)).2]
      _ = (X ^ d) ^ R := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = X ^ (R * d) := by rw [← pow_mul, mul_comm]
      _ ≤ N := hXN
  refine ⟨A, ?_, ?_, ?_⟩
  · intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨g, hg, rfl⟩ := hn
    exact Finset.mem_Icc.mpr ⟨hΦ_pos g hg, hΦ_le g hg⟩
  · -- ¬ HasEqualLcmTuple k A
    rintro ⟨T, hTA, hTcard, L, hTlcm⟩
    have hT_pos : ∀ a ∈ T, a ≠ 0 := by
      intro a ha
      have haA := hTA ha
      rw [Finset.mem_image] at haA
      obtain ⟨g, hg, rfl⟩ := haA
      have := hΦ_pos g hg; omega
    have hL_ne : L ≠ 0 := by
      have h2 : 1 < T.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
      rw [← hTlcm a ha b hb hab]
      exact Nat.lcm_ne_zero (hT_pos a ha) (hT_pos b hb)
    -- Every a ∈ T has a unique preimage g ∈ Ω, so |(a.primeFactors ∩ P r)| = d for every r
    have hcard_r : ∀ a ∈ T, ∀ r : Fin R, (a.primeFactors ∩ P r).card = d := by
      intro a ha r
      have haA := hTA ha
      rw [Finset.mem_image] at haA
      obtain ⟨g, hg, rfl⟩ := haA
      rw [hΦ_inter g hg r]
      rw [Fintype.mem_piFinset] at hg
      exact (Finset.mem_powersetCard.mp (hg r)).2
    -- Every distinct pair a, b ∈ T satisfies (a.primeFactors ∩ P r) ∪ (b.primeFactors ∩ P r) = L.primeFactors ∩ P r
    have hunion_r : ∀ r : Fin R, ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
        (a.primeFactors ∩ P r) ∪ (b.primeFactors ∩ P r) = L.primeFactors ∩ P r := by
      intro r a ha b hb hab
      rw [← Finset.union_inter_distrib_right, ← primeFactors_lcm_eq_union (hT_pos a ha) (hT_pos b hb),
        hTlcm a ha b hb hab]
    -- Find some block r where a ↦ a.primeFactors ∩ P r is NOT constant on T
    have hex_r : ∃ r : Fin R, ∃ a1 ∈ T, ∃ a2 ∈ T, a1.primeFactors ∩ P r ≠ a2.primeFactors ∩ P r := by
      have h2 : 1 < T.card := by omega
      obtain ⟨a1, ha1, a2, ha2, hne⟩ := Finset.one_lt_card.mp h2
      by_contra hall
      push Not at hall
      have ha1A := hTA ha1; rw [Finset.mem_image] at ha1A; obtain ⟨g1, hg1, rfl⟩ := ha1A
      have ha2A := hTA ha2; rw [Finset.mem_image] at ha2A; obtain ⟨g2, hg2, rfl⟩ := ha2A
      have hg12 : g1 = g2 := by
        funext r
        rw [← hΦ_inter g1 hg1 r, ← hΦ_inter g2 hg2 r]
        exact hall r (Φ g1) ha1 (Φ g2) ha2
      exact hne (by rw [hg12])
    obtain ⟨r, a1, ha1, a2, ha2, ha12_ne⟩ := hex_r
    let Fr : ℕ → Finset ℕ := fun a => a.primeFactors ∩ P r
    let Lr : Finset ℕ := L.primeFactors ∩ P r
    -- Claim 1: Fr is injective on T!
    have hFr_inj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Fr a ≠ Fr b := by
      intro a ha b hb hab heq
      have hLr : Fr a = Lr := by
        have h1 := hunion_r r a ha b hb hab
        change Fr a ∪ Fr b = Lr at h1
        rw [heq, Finset.union_idempotent] at h1
        exact heq.trans h1
      have hconst : ∀ c ∈ T, Fr c = Fr a := by
        intro c hc
        have hsub : Fr c ⊆ Lr := by
          have hex_x : ∃ x ∈ T, x ≠ c := by
            have h2 : 1 < T.card := by omega
            obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
            by_cases huc : u = c
            · exact ⟨v, hv, fun h => huv (huc.trans h.symm)⟩
            · exact ⟨u, hu, huc⟩
          obtain ⟨x, hx, hxc⟩ := hex_x
          have := hunion_r r c hc x hx (Ne.symm hxc)
          change Fr c ∪ Fr x = Lr at this
          rw [← this]; exact Finset.subset_union_left
        rw [← hLr] at hsub
        exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_r c hc r, hcard_r a ha r])
      exact ha12_ne ((hconst a1 ha1).trans (hconst a2 ha2).symm)
    -- Claim 2: For every a ∈ T, C a := Lr \ Fr a is nonempty
    let C : ℕ → Finset ℕ := fun a => Lr \ Fr a
    have hC_nonempty : ∀ a ∈ T, (C a).Nonempty := by
      intro a ha
      have hsub_a : Fr a ⊆ Lr := by
        have hex_b : ∃ b ∈ T, b ≠ a := by
          have h2 : 1 < T.card := by omega
          obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
          by_cases hua : u = a
          · exact ⟨v, hv, fun h => huv (hua.trans h.symm)⟩
          · exact ⟨u, hu, hua⟩
        obtain ⟨b, hb, hba⟩ := hex_b
        have := hunion_r r a ha b hb (Ne.symm hba)
        change Fr a ∪ Fr b = Lr at this
        rw [← this]; exact Finset.subset_union_left
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
      have hEqLr : Fr a = Lr := Finset.Subset.antisymm hsub_a hemp
      -- Pick any b ∈ T with b ≠ a: Fr b ⊆ Lr = Fr a and equal card forces Fr b = Fr a!
      have hex_b : ∃ b ∈ T, b ≠ a := by
        have h2 : 1 < T.card := by omega
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
        by_cases hua : u = a
        · exact ⟨v, hv, fun h => huv (hua.trans h.symm)⟩
        · exact ⟨u, hu, hua⟩
      obtain ⟨b, hb, hba⟩ := hex_b
      have hsub_b : Fr b ⊆ Fr a := by
        rw [hEqLr]
        have := hunion_r r b hb a ha hba
        change Fr b ∪ Fr a = Lr at this
        rw [← this]; exact Finset.subset_union_left
      have hEqba : Fr b = Fr a :=
        Finset.eq_of_subset_of_card_le hsub_b (by rw [hcard_r b hb r, hcard_r a ha r])
      exact hFr_inj b hb a ha hba hEqba
    -- Claim 3: C a and C b are disjoint for distinct a, b ∈ T
    have hC_disj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint (C a) (C b) := by
      intro a ha b hb hab
      rw [Finset.disjoint_left]; intro p hpa hpb
      simp only [C, Finset.mem_sdiff] at hpa hpb
      have hun := hunion_r r a ha b hb hab
      change Fr a ∪ Fr b = Lr at hun
      rw [← hun, Finset.mem_union] at hpa
      rcases hpa.1 with h | h
      · exact hpa.2 h
      · exact hpb.2 h
    -- Contradiction: for a1 ∈ T, (T.erase a1).biUnion C ⊆ Fr a1!
    have hbi_sub : (T.erase a1).biUnion C ⊆ Fr a1 := by
      intro p hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨b, hb, hpb⟩ := hp
      rw [Finset.mem_erase] at hb
      simp only [C, Finset.mem_sdiff] at hpb
      have hun := hunion_r r a1 ha1 b hb.2 (Ne.symm hb.1)
      change Fr a1 ∪ Fr b = Lr at hun
      rw [← hun, Finset.mem_union] at hpb
      rcases hpb.1 with h | h
      · exact h
      · exact False.elim (hpb.2 h)
    have hcard_lb : k - 1 ≤ ((T.erase a1).biUnion C).card := by
      rw [Finset.card_biUnion (fun b1 hb1 b2 hb2 hne =>
        hC_disj b1 (Finset.mem_of_mem_erase hb1) b2 (Finset.mem_of_mem_erase hb2) hne)]
      calc k - 1 = (T.erase a1).card := by rw [Finset.card_erase_of_mem ha1, hTcard]
        _ = ∑ _b ∈ T.erase a1, 1 := by simp
        _ ≤ ∑ b ∈ T.erase a1, (C b).card :=
            Finset.sum_le_sum fun b hb => Finset.card_pos.mpr (hC_nonempty b (Finset.mem_of_mem_erase hb))
    have hcard_ub : ((T.erase a1).biUnion C).card ≤ d := by
      rw [← hcard_r a1 ha1 r]
      exact Finset.card_le_card hbi_sub
    omega
  · -- Exact harmonic sum of A
    calc ∑ n ∈ A, (n : ℝ)⁻¹
        = ∑ g ∈ Ω, (Φ g : ℝ)⁻¹ :=
          Finset.sum_image (fun g1 hg1 g2 hg2 h => hΦ_inj hg1 hg2 h)
      _ = ∑ g ∈ Ω, ∏ r : Fin R, ∏ p ∈ g r, (p : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl fun g _ => ?_
          unfold Φ
          rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl fun r _ => ?_
          rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
      _ = ∏ r : Fin R, ∑ S ∈ (P r).powersetCard d, ∏ p ∈ S, (p : ℝ)⁻¹ := by
          symm
          exact Finset.prod_univ_sum (fun r => (P r).powersetCard d)
            (fun r S => ∏ p ∈ S, (p : ℝ)⁻¹)

/- ### Section 5: Asymptotic optimization and main theorem -/

private lemma exists_good_delta (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      let x := Real.exp 1 * ((d.factorial : ℕ) : ℝ) ^ (1 / (d : ℝ))
      (d : ℝ) * δ < x ∧
      (d : ℝ) / x - ε / 2 < Real.log ((x - (d : ℝ) * δ) ^ d / (d.factorial : ℝ)) / (x + δ) := by
  set x : ℝ := Real.exp 1 * ((d.factorial : ℕ) : ℝ) ^ (1 / (d : ℝ))
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hfac_pos : (0 : ℝ) < (d.factorial : ℝ) := by positivity
  have hx_pos : 0 < x := by positivity
  -- At δ = 0, the value is log (x^d / d!) / x = log (e^d) / x = d / x!
  have hxd : x ^ d / (d.factorial : ℝ) = Real.exp (d : ℝ) := by
    have hpow : x ^ d = Real.exp (d : ℝ) * (d.factorial : ℝ) := by
      calc x ^ d = (Real.exp 1) ^ d * (((d.factorial : ℝ) ^ (1 / (d : ℝ))) ^ d) := by
            rw [mul_pow]
        _ = Real.exp (d : ℝ) * ((d.factorial : ℝ) ^ ((1 / (d : ℝ)) * (d : ℝ))) := by
            rw [← Real.exp_nat_mul, mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hfac_pos)]
        _ = Real.exp (d : ℝ) * (d.factorial : ℝ) := by
            rw [one_div_mul_cancel (ne_of_gt hd_pos), Real.rpow_one]
    rw [hpow, mul_div_cancel_right₀ _ (ne_of_gt hfac_pos)]
  let F : ℝ → ℝ := fun t => Real.log ((x - (d : ℝ) * t) ^ d / (d.factorial : ℝ)) / (x + t)
  have hF0 : F 0 = (d : ℝ) / x := by
    simp only [F, mul_zero, sub_zero, add_zero, hxd, Real.log_exp]
  have hcont' : ContinuousAt F 0 := by
    have hinner : ContinuousAt (fun t : ℝ => (x - (d : ℝ) * t) ^ d / (d.factorial : ℝ)) 0 :=
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow d).div_const _
    have hlog : ContinuousAt (fun t : ℝ => Real.log ((x - (d : ℝ) * t) ^ d / (d.factorial : ℝ))) 0 :=
      ContinuousAt.log hinner (by simp only [mul_zero, sub_zero, hxd]; exact ne_of_gt (Real.exp_pos _))
    exact hlog.div (continuousAt_const.add continuousAt_id) (by simp; exact ne_of_gt hx_pos)
  rw [Metric.continuousAt_iff] at hcont'
  obtain ⟨r, hr_pos, hr⟩ := hcont' (ε / 2) (by linarith)
  refine ⟨min (r / 2) (x / (2 * d)), by positivity, ?_, ?_⟩
  · have hle : min (r / 2) (x / (2 * d)) ≤ x / (2 * d) := min_le_right _ _
    have hmul : (d : ℝ) * min (r / 2) (x / (2 * d)) ≤ (d : ℝ) * (x / (2 * d)) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hd_pos)
    have heq : (d : ℝ) * (x / (2 * d)) = x / 2 := by field_simp
    linarith
  · set δ := min (r / 2) (x / (2 * d))
    have hδ_pos : 0 < δ := by positivity
    have hdist : dist δ 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hF := hr hdist
    rw [Real.dist_eq, hF0] at hF
    linarith [(abs_lt.mp hF).1]

private lemma real_log_le_linear_mul (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, Real.log t ≤ c * t := by
  have h := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)
  rw [Asymptotics.isLittleO_iff] at h
  filter_upwards [h hc, Filter.eventually_ge_atTop (1 : ℝ)] with t ht ht1
  simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht1),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] at ht
  exact ht

private lemma prime_tail_sum_ge {P₀ X : ℕ} (hX : 3 ≤ X) :
    Real.log (Real.log (X : ℝ)) - (1 + ∑ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime, ((p : ℝ)⁻¹)) ≤
      ∑ p ∈ (Finset.Icc P₀ X).filter Nat.Prime, ((p : ℝ)⁻¹) := by
  have hfull := prime_harmonic_lower_bound hX
  have hcov : (Finset.Icc 1 X).filter Nat.Prime ⊆
      (Finset.Icc 1 P₀).filter Nat.Prime ∪ (Finset.Icc P₀ X).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    rcases le_or_gt p P₀ with hle | hgt
    · left; exact ⟨⟨hp.1.1, hle⟩, hp.2⟩
    · right; exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have h1 : ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, ((p : ℝ)⁻¹) ≤
      ∑ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime ∪ (Finset.Icc P₀ X).filter Nat.Prime, ((p : ℝ)⁻¹) :=
    Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ => by positivity)
  have h2 := Finset.sum_union_inter (s₁ := (Finset.Icc 1 P₀).filter Nat.Prime)
    (s₂ := (Finset.Icc P₀ X).filter Nat.Prime) (f := fun p : ℕ => (p : ℝ)⁻¹)
  have h3 : 0 ≤ ∑ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime ∩ (Finset.Icc P₀ X).filter Nat.Prime, ((p : ℝ)⁻¹) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  linarith

private lemma tang_zhang_step {k N R X P₀ : ℕ} {x δ γ : ℝ}
    (hk : 3 ≤ k) (hx : 0 < x) (hδ : 0 < δ)
    (hδ_small : ((k - 2 : ℕ) : ℝ) * δ < x)
    (hγ_eq : γ = Real.log ((x - ((k - 2 : ℕ) : ℝ) * δ) ^ (k - 2) / ((k - 2).factorial : ℝ)))
    (hP₀_inv : ∀ p : ℕ, P₀ ≤ p → (p : ℝ)⁻¹ ≤ δ)
    (hXN : X ^ (R * (k - 2)) ≤ N)
    (hsum : (R : ℝ) * (x + δ) ≤ ∑ p ∈ (Finset.Icc P₀ X).filter Nat.Prime, ((p : ℝ)⁻¹)) :
    Real.exp (γ * R) ≤ Erdos856.f k N := by
  let S_primes := (Finset.Icc P₀ X).filter Nat.Prime
  obtain ⟨P, hP_sub, hP_disj, hP_lo⟩ := exists_disjoint_chunks R (S := S_primes)
    (f := fun p => (p : ℝ)⁻¹)
    (fun _ _ => by positivity)
    (fun p hp => hP₀_inv p (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)
    (le_of_lt hx) (le_of_lt hδ) hsum
  obtain ⟨A, hA_sub, hA_free, hA_sum⟩ := block_product_construction hk P
    (fun r p hp => (Finset.mem_filter.mp (hP_sub r hp)).2)
    (fun r p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hP_sub r hp)).1).2)
    hP_disj hXN
  have hblock_lb : ∀ r : Fin R, Real.exp γ ≤ ∑ S ∈ (P r).powersetCard (k - 2), ∏ p ∈ S, (p : ℝ)⁻¹ := by
    intro r
    have hW_ge : x ≤ ∑ p ∈ P r, (p : ℝ)⁻¹ := hP_lo r
    have hW_dδ : ((k - 2 : ℕ) : ℝ) * δ ≤ ∑ p ∈ P r, (p : ℝ)⁻¹ := le_trans (le_of_lt hδ_small) hW_ge
    have hbase_pos : 0 < (x - ((k - 2 : ℕ) : ℝ) * δ) ^ (k - 2) / ((k - 2).factorial : ℝ) := by
      have : 0 < x - ((k - 2 : ℕ) : ℝ) * δ := by linarith
      positivity
    calc Real.exp γ
        = (x - ((k - 2 : ℕ) : ℝ) * δ) ^ (k - 2) / ((k - 2).factorial : ℝ) := by
            rw [hγ_eq, Real.exp_log hbase_pos]
      _ ≤ (∑ p ∈ P r, (p : ℝ)⁻¹ - ((k - 2 : ℕ) : ℝ) * δ) ^ (k - 2) / ((k - 2).factorial : ℝ) := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left₀ (by linarith) (by linarith) (k - 2)
      _ ≤ ∑ S ∈ (P r).powersetCard (k - 2), ∏ p ∈ S, (p : ℝ)⁻¹ :=
            elemSym_lower_bound (P r) (fun p => (p : ℝ)⁻¹) δ
              (fun _ _ => by positivity)
              (fun p hp => hP₀_inv p (Finset.mem_Icc.mp (Finset.mem_filter.mp (hP_sub r hp)).1).1)
              (le_of_lt hδ) (k - 2) hW_dδ
  have hprod_lb : Real.exp (γ * R) ≤ ∑ n ∈ A, (n : ℝ)⁻¹ := by
    rw [hA_sum]
    calc Real.exp (γ * R)
        = (Real.exp γ) ^ R := by rw [mul_comm, Real.exp_nat_mul]
      _ = ∏ _r : Fin R, Real.exp γ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ r : Fin R, ∑ S ∈ (P r).powersetCard (k - 2), ∏ p ∈ S, (p : ℝ)⁻¹ :=
          Finset.prod_le_prod (fun _ _ => le_of_lt (Real.exp_pos _)) (fun r _ => hblock_lb r)
  exact le_trans hprod_lb (Erdos856.sum_le_f hA_sub hA_free)

private lemma tang_zhang_for_N {k N P₀ : ℕ} {x δ γ η ε Csmall : ℝ}
    (hk : 3 ≤ k) (hε : 0 < ε) (hx : 0 < x) (hδ : 0 < δ) (hγ : 0 < γ)
    (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4)
    (hδ_small : ((k - 2 : ℕ) : ℝ) * δ < x)
    (hγ_eq : γ = Real.log ((x - ((k - 2 : ℕ) : ℝ) * δ) ^ (k - 2) / ((k - 2).factorial : ℝ)))
    (hγ_def : Erdos856.tangZhangExponent k - ε / 2 < γ / (x + δ))
    (hη_prod : η * (γ / (x + δ)) ≤ ε / 4)
    (hP₀_inv : ∀ p : ℕ, P₀ ≤ p → (p : ℝ)⁻¹ ≤ δ)
    (hCsmall : Csmall = 1 + ∑ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime, ((p : ℝ)⁻¹))
    (hN20 : 20 ≤ N)
    (hLL_10 : 10 ≤ Real.log (Real.log (N : ℝ)))
    (hLL_R : 4 * (x + δ) / (1 - η) ≤ Real.log (Real.log (N : ℝ)))
    (hLL_C : 4 * (Csmall + 2) / η ≤ Real.log (Real.log (N : ℝ)))
    (hLL_γ : 4 * γ / ε ≤ Real.log (Real.log (N : ℝ)))
    (hN2 : Real.log ((2 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * Real.log (Real.log (N : ℝ))) ≤
      (η / (4 * (2 * ((k - 2 : ℕ) : ℝ) / (x + δ)))) * ((2 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * Real.log (Real.log (N : ℝ))))
    (hN3 : (4 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ)) :
    Real.log (N : ℝ) ^ (Erdos856.tangZhangExponent k - ε) ≤ Erdos856.f k N := by
  have hd_pos : (0 : ℝ) < ((k - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 2)
  have hxd_pos : 0 < x + δ := by linarith
  have h1mη_pos : (0 : ℝ) < 1 - η := by linarith
  have hL_pos : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos; exact_mod_cast (by omega : 1 < N)
  have hLL_pos : 0 < Real.log (Real.log (N : ℝ)) := by linarith
  set R : ℕ := Nat.floor ((1 - η) * Real.log (Real.log (N : ℝ)) / (x + δ))
  have hR_le : (R : ℝ) ≤ (1 - η) * Real.log (Real.log (N : ℝ)) / (x + δ) :=
    Nat.floor_le (by positivity)
  have hR_gt : (1 - η) * Real.log (Real.log (N : ℝ)) / (x + δ) - 1 < (R : ℝ) :=
    Nat.sub_one_lt_floor _
  have hR_pos : 1 ≤ R := by
    have : (3 : ℝ) < (R : ℝ) := by
      have hmul : 4 * (x + δ) ≤ (1 - η) * Real.log (Real.log (N : ℝ)) := by
        have := (div_le_iff₀ h1mη_pos).mp hLL_R; linarith
      have hdiv : 4 ≤ (1 - η) * Real.log (Real.log (N : ℝ)) / (x + δ) := (le_div_iff₀ hxd_pos).mpr hmul
      linarith
    exact_mod_cast le_of_lt (by linarith : (1 : ℝ) < R)
  have hdR_pos : (0 : ℝ) < ((k - 2 : ℕ) : ℝ) * R := by positivity
  set X : ℕ := Nat.floor (Real.exp (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R)))
  have hXN : X ^ (R * (k - 2)) ≤ N := by
    have hX_le : (X : ℝ) ≤ Real.exp (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R)) :=
      Nat.floor_le (le_of_lt (Real.exp_pos _))
    have hpow : ((X ^ (R * (k - 2)) : ℕ) : ℝ) ≤ (N : ℝ) := by
      rw [Nat.cast_pow]
      calc (X : ℝ) ^ (R * (k - 2))
          ≤ (Real.exp (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R))) ^ (R * (k - 2)) :=
            pow_le_pow_left₀ (Nat.cast_nonneg X) hX_le (R * (k - 2))
        _ = Real.exp (((R * (k - 2) : ℕ) : ℝ) * (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R))) := by
            rw [← Real.exp_nat_mul]
        _ = Real.exp (Real.log (N : ℝ)) := by
            congr 1; rw [Nat.cast_mul]; field_simp
        _ = N := Real.exp_log (by positivity)
    exact_mod_cast hpow
  have hR_le_simple : (R : ℝ) ≤ Real.log (Real.log (N : ℝ)) / (x + δ) := by
    have : (1 - η) * Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (N : ℝ)) := by nlinarith
    exact le_trans hR_le (div_le_div_of_nonneg_right this (le_of_lt hxd_pos))
  have hLdR_ge2 : 2 ≤ Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R) := by
    rw [le_div_iff₀ hdR_pos]
    have h1 : ((k - 2 : ℕ) : ℝ) * R ≤ ((k - 2 : ℕ) : ℝ) * (Real.log (Real.log (N : ℝ)) / (x + δ)) :=
      mul_le_mul_of_nonneg_left hR_le_simple (le_of_lt hd_pos)
    have h2 : 2 * (((k - 2 : ℕ) : ℝ) * (Real.log (Real.log (N : ℝ)) / (x + δ))) =
        2 * (((k - 2 : ℕ) : ℝ) / (x + δ) * Real.log (Real.log (N : ℝ))) := by ring
    have h3 : (4 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * Real.log (Real.log (N : ℝ)) =
        4 * (((k - 2 : ℕ) : ℝ) / (x + δ) * Real.log (Real.log (N : ℝ))) := by ring
    have hnn : 0 ≤ ((k - 2 : ℕ) : ℝ) / (x + δ) * Real.log (Real.log (N : ℝ)) := by positivity
    linarith
  have hexp_ge4 : (4 : ℝ) ≤ Real.exp (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R)) := by
    have h2 : (2 : ℝ) * 2 ≤ Real.exp 1 * Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); nlinarith
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have hle : Real.exp 2 ≤ Real.exp (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R)) :=
      Real.exp_le_exp.mpr hLdR_ge2
    linarith
  have hX_ge3 : 3 ≤ X := by
    have hlt : Real.exp (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R)) - 1 < (X : ℝ) :=
      Nat.sub_one_lt_floor _
    have : (3 : ℝ) < X := by linarith
    exact_mod_cast le_of_lt this
  have hlogX_ge : Real.log (N : ℝ) / (2 * ((k - 2 : ℕ) : ℝ) * R) ≤ Real.log (X : ℝ) := by
    have hX_gt : Real.exp (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R)) / 2 ≤ (X : ℝ) := by
      have hlt : Real.exp (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R)) - 1 < (X : ℝ) :=
        Nat.sub_one_lt_floor _
      linarith
    have hlog1 : Real.log (Real.exp (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R)) / 2) ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by positivity) hX_gt
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num), Real.log_exp] at hlog1
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hhalf : Real.log (N : ℝ) / (2 * ((k - 2 : ℕ) : ℝ) * R) =
        (Real.log (N : ℝ) / (((k - 2 : ℕ) : ℝ) * R)) / 2 := by ring
    linarith
  have hloglogX_ge : Real.log (Real.log (N : ℝ)) - Real.log (2 * ((k - 2 : ℕ) : ℝ) * R) ≤
      Real.log (Real.log (X : ℝ)) := by
    have hpos : 0 < Real.log (N : ℝ) / (2 * ((k - 2 : ℕ) : ℝ) * R) := by positivity
    calc Real.log (Real.log (N : ℝ)) - Real.log (2 * ((k - 2 : ℕ) : ℝ) * R)
        = Real.log (Real.log (N : ℝ) / (2 * ((k - 2 : ℕ) : ℝ) * R)) :=
          (Real.log_div (ne_of_gt hL_pos) (by positivity)).symm
      _ ≤ Real.log (Real.log (X : ℝ)) := Real.log_le_log hpos hlogX_ge
  have hlog2dR : Real.log (2 * ((k - 2 : ℕ) : ℝ) * R) ≤ (η / 4) * Real.log (Real.log (N : ℝ)) := by
    have hle : 2 * ((k - 2 : ℕ) : ℝ) * R ≤
        (2 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * Real.log (Real.log (N : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hR_le_simple (show (0 : ℝ) ≤ 2 * ((k - 2 : ℕ) : ℝ) by positivity)
      linarith [show 2 * ((k - 2 : ℕ) : ℝ) * (Real.log (Real.log (N : ℝ)) / (x + δ)) =
        (2 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * Real.log (Real.log (N : ℝ)) by ring]
    have h1 := Real.log_le_log (by positivity : (0 : ℝ) < 2 * ((k - 2 : ℕ) : ℝ) * R) hle
    have h3' : (η / (4 * (2 * ((k - 2 : ℕ) : ℝ) / (x + δ)))) *
        ((2 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * Real.log (Real.log (N : ℝ))) =
        (η / 4) * Real.log (Real.log (N : ℝ)) := by
      have hne : 2 * ((k - 2 : ℕ) : ℝ) / (x + δ) ≠ 0 := by positivity
      field_simp
    exact le_trans h1 (h3' ▸ hN2)
  have hS_sum : (R : ℝ) * (x + δ) ≤ ∑ p ∈ (Finset.Icc P₀ X).filter Nat.Prime, ((p : ℝ)⁻¹) := by
    have htail := prime_tail_sum_ge (P₀ := P₀) hX_ge3
    rw [← hCsmall] at htail
    have hC_le : Csmall ≤ (η / 4) * Real.log (Real.log (N : ℝ)) := by
      have := (div_le_iff₀ hη_pos).mp hLL_C; linarith
    have hRxd : (R : ℝ) * (x + δ) ≤ (1 - η) * Real.log (Real.log (N : ℝ)) :=
      (le_div_iff₀ hxd_pos).mp hR_le
    have hη_LL : 0 ≤ η * Real.log (Real.log (N : ℝ)) := mul_nonneg (le_of_lt hη_pos) (le_of_lt hLL_pos)
    linarith
  have hstep_f : Real.exp (γ * R) ≤ Erdos856.f k N :=
    tang_zhang_step hk hx hδ hδ_small hγ_eq hP₀_inv hXN hS_sum
  have hexp_ge : (Erdos856.tangZhangExponent k - ε) * Real.log (Real.log (N : ℝ)) ≤ γ * R := by
    have hR_lb : (1 - η) * (γ / (x + δ)) * Real.log (Real.log (N : ℝ)) - γ ≤ γ * R := by
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt hR_gt) (le_of_lt hγ)
      linarith [show γ * ((1 - η) * Real.log (Real.log (N : ℝ)) / (x + δ) - 1) =
        (1 - η) * (γ / (x + δ)) * Real.log (Real.log (N : ℝ)) - γ by ring]
    have hcoef : Erdos856.tangZhangExponent k - 3 * ε / 4 ≤ (1 - η) * (γ / (x + δ)) := by
      linarith [show (1 - η) * (γ / (x + δ)) = γ / (x + δ) - η * (γ / (x + δ)) by ring]
    have hγ_le : γ ≤ (ε / 4) * Real.log (Real.log (N : ℝ)) := by
      have := (div_le_iff₀ hε).mp hLL_γ; linarith
    have hmul_c := mul_le_mul_of_nonneg_right hcoef (le_of_lt hLL_pos)
    linarith [show (Erdos856.tangZhangExponent k - 3 * ε / 4) * Real.log (Real.log (N : ℝ)) -
      (ε / 4) * Real.log (Real.log (N : ℝ)) =
      (Erdos856.tangZhangExponent k - ε) * Real.log (Real.log (N : ℝ)) by ring]
  calc Real.log (N : ℝ) ^ (Erdos856.tangZhangExponent k - ε)
      = Real.exp ((Erdos856.tangZhangExponent k - ε) * Real.log (Real.log (N : ℝ))) := by
        rw [Real.rpow_def_of_pos hL_pos, mul_comm]
    _ ≤ Real.exp (γ * R) := Real.exp_le_exp.mpr hexp_ge
    _ ≤ Erdos856.f k N := hstep_f

private lemma tang_zhang_lower_main (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ (Erdos856.tangZhangExponent k - ε) ≤ Erdos856.f k N := by
  have hd : 1 ≤ k - 2 := by omega
  have hd_cast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ k)]; norm_num
  set x : ℝ := Real.exp 1 * (((k - 2).factorial : ℕ) : ℝ) ^ (1 / ((k - 2 : ℕ) : ℝ))
  have hx_pos : 0 < x := by positivity
  have htz_eq : Erdos856.tangZhangExponent k = ((k - 2 : ℕ) : ℝ) / x := by
    unfold Erdos856.tangZhangExponent
    rw [← hd_cast]
  obtain ⟨δ, hδ_pos, hδ_small, hγ_ratio⟩ := exists_good_delta (k - 2) hd ε hε
  set γ : ℝ := Real.log ((x - ((k - 2 : ℕ) : ℝ) * δ) ^ (k - 2) / ((k - 2).factorial : ℝ)) with hγ_eq
  have hγ_def : Erdos856.tangZhangExponent k - ε / 2 < γ / (x + δ) := by
    rw [htz_eq]; exact hγ_ratio
  have hxd_pos : 0 < x + δ := by linarith
  obtain ⟨P₀, hP₀⟩ := exists_nat_gt (max (2 : ℝ) (1 / δ))
  have hP₀_inv : ∀ p : ℕ, P₀ ≤ p → (p : ℝ)⁻¹ ≤ δ := by
    intro p hp
    have h1 : 1 / δ < P₀ := lt_of_le_of_lt (le_max_right _ _) hP₀
    have h2 : (P₀ : ℝ) ≤ p := by exact_mod_cast hp
    have h3 : 1 / δ < p := lt_of_lt_of_le h1 h2
    have hP₀_pos : (0 : ℝ) < P₀ := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_left _ _) hP₀)
    have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le hP₀_pos h2
    rw [inv_le_comm₀ hp_pos hδ_pos]
    rw [one_div] at h3
    linarith
  by_cases hneg : Erdos856.tangZhangExponent k - ε ≤ 0
  · filter_upwards [Filter.eventually_ge_atTop 3] with N hN
    have hlog1 : 1 ≤ Real.log (N : ℝ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith [Real.exp_one_lt_d9]
    have hpow_le1 : Real.log (N : ℝ) ^ (Erdos856.tangZhangExponent k - ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlog1 hneg
    have h1_le_f : (1 : ℝ) ≤ Erdos856.f k N := by
      have hsub : ({1} : Finset ℕ) ⊆ Finset.Icc 1 N := by
        intro a ha; simp only [Finset.mem_singleton] at ha; subst ha; simp; omega
      have hfree : ¬ Erdos856.HasEqualLcmTuple k {1} := by
        rintro ⟨S, hS, hSc, _⟩
        have := Finset.card_le_card hS; simp at this; omega
      have hle := Erdos856.sum_le_f hsub hfree
      simp at hle; exact hle
    linarith
  · push Not at hneg
    have hγ_ratio_pos : 0 < γ / (x + δ) := by linarith
    have hγ_pos : 0 < γ := (div_pos_iff_of_pos_right hxd_pos).mp hγ_ratio_pos
    set η : ℝ := min (1 / 4) ((ε / 4) / (γ / (x + δ)))
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 4 := min_le_left _ _
    have hη_prod : η * (γ / (x + δ)) ≤ ε / 4 :=
      (le_div_iff₀ hγ_ratio_pos).mp (min_le_right _ _)
    set Csmall : ℝ := 1 + ∑ p ∈ (Finset.Icc 1 P₀).filter Nat.Prime, ((p : ℝ)⁻¹) with hCsmall
    have hd_pos : (0 : ℝ) < ((k - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 2)
    have hlog_lin := real_log_le_linear_mul (η / (4 * (2 * ((k - 2 : ℕ) : ℝ) / (x + δ)))) (by positivity)
    have hLL_atTop : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hL_atTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h1 := hLL_atTop.eventually (Filter.eventually_ge_atTop (max 10 (max ((4 * (x + δ)) / (1 - η))
      (max (4 * (Csmall + 2) / η) (4 * γ / ε)))))
    have h2 := hLL_atTop.eventually (Filter.eventually_map.mp (by
      have hscale : Tendsto (fun u : ℝ => (2 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * u) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
      exact hscale.eventually hlog_lin))
    have h3 : ∀ᶠ N : ℕ in atTop,
        (4 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
      have hlin2 := real_log_le_linear_mul (1 / (4 * ((k - 2 : ℕ) : ℝ) / (x + δ))) (by positivity)
      filter_upwards [hL_atTop.eventually hlin2] with N hN
      have hpos : (0 : ℝ) < 4 * ((k - 2 : ℕ) : ℝ) / (x + δ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hN (le_of_lt hpos)
      have hcancel : (4 * ((k - 2 : ℕ) : ℝ) / (x + δ)) *
          (1 / (4 * ((k - 2 : ℕ) : ℝ) / (x + δ)) * Real.log (N : ℝ)) = Real.log (N : ℝ) := by field_simp
      linarith
    filter_upwards [h1, h2, h3, Filter.eventually_ge_atTop 20] with N hN1 hN2 hN3 hN20
    exact tang_zhang_for_N hk hε hx_pos hδ_pos hγ_pos hη_pos hη_le hδ_small hγ_eq hγ_def hη_prod
      hP₀_inv hCsmall hN20
      (le_trans (le_max_left _ _) hN1)
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN1)
      (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hN1)
      (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hN1)
      hN2 hN3

end Erdos856TangZhang

theorem OMA.solution : type_of% @Erdos856.erdos_856.variants.tang_zhang_lower := by
  exact Erdos856TangZhang.tang_zhang_lower_main
