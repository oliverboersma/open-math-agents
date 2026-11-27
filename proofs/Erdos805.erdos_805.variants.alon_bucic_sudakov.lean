import FormalConjectures.ErdosProblems.«805»
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem 805 — Alon–Bucić–Sudakov (2021)

Direct formalization of Theorem 8 and Theorem 2 of Alon–Bucić–Sudakov (2021, arXiv:2004.04718),
proving `Erdos805.erdos_805.variants.alon_bucic_sudakov`.
-/

-- Problem: Erdős Problem 805 — alon bucic sudakov
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/805.lean:126 (declaration Erdos805.erdos_805.variants.alon_bucic_sudakov)
-- Credit: @kDylanHayes

namespace Erdos805ABS

open Finset Filter Real SimpleGraph Erdos805

-- ### Part 1: Finite Bernoulli Product Weights, Chernoff, Erdos 1947, and Scrambling (Lemma 7)

private abbrev EdgePair (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

private def prob {E : Type*} [Fintype E] (p : ℝ) (f : E → Bool) : ℝ :=
  ∏ e : E, if f e then p else 1 - p

private lemma prob_nonneg {E : Type*} [Fintype E] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : E → Bool) : 0 ≤ prob p f := by
  unfold prob
  apply Finset.prod_nonneg
  intro e _
  cases f e <;> simp <;> linarith

private lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {s t : Finset α}
    {g : α → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∑ x ∈ s ∪ t, g x ≤ ∑ x ∈ s, g x + ∑ x ∈ t, g x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := g)
  have hi : 0 ≤ ∑ x ∈ s ∩ t, g x := Finset.sum_nonneg (fun x _ => hg x)
  linarith

private lemma sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {s : Finset ι} {t : ι → Finset α} {g : α → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∑ x ∈ s.biUnion t, g x ≤ ∑ i ∈ s, ∑ x ∈ t i, g x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h1 := sum_union_le_of_nonneg (s := t a) (t := s.biUnion t) hg
    linarith

private lemma sum_prob_eq_one {E : Type*} [Fintype E] [DecidableEq E] (p : ℝ) :
    ∑ f : E → Bool, prob p f = 1 := by
  unfold prob
  rw [← Fintype.prod_sum (fun (_ : E) (b : Bool) => if b then p else 1 - p)]
  simp

private lemma sum_prob_all_eq {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (S : Finset E) (b : E → Bool) :
    ∑ f ∈ Finset.univ.filter (fun f : E → Bool => ∀ e ∈ S, f e = b e), prob p f =
      ∏ e ∈ S, if b e then p else 1 - p := by
  classical
  let w : E → Bool → ℝ := fun e x =>
    if e ∈ S then (if x = b e then (if x then p else 1 - p) else 0)
    else (if x then p else 1 - p)
  have hprod_sum : ∑ f : E → Bool, ∏ e : E, w e (f e) =
      ∏ e ∈ S, if b e then p else 1 - p := by
    rw [← Fintype.prod_sum w]
    have h1 : ∀ e : E, ∑ x : Bool, w e x = if e ∈ S then (if b e then p else 1 - p) else 1 := by
      intro e
      by_cases he : e ∈ S
      · simp only [w, if_pos he]
        cases hbe : b e <;> simp
      · simp only [w, if_neg he]
        simp
    simp only [h1, Finset.prod_ite_mem, Finset.univ_inter]
  rw [← hprod_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun f : E → Bool => ∀ e ∈ S, f e = b e)]
  have hzero : ∑ f ∈ Finset.univ.filter (fun f : E → Bool => ¬ ∀ e ∈ S, f e = b e),
      ∏ e : E, w e (f e) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    have hnot := (Finset.mem_filter.mp hf).2
    push Not at hnot
    obtain ⟨e, heS, hne⟩ := hnot
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [w, heS, hne]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hall := (Finset.mem_filter.mp hf).2
  unfold prob
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases he : e ∈ S
  · simp [w, he, hall e he]
  · simp [w, he]

private lemma chernoff_mgf {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (S : Finset E) (lam : ℝ) :
    ∑ f : E → Bool, prob p f * Real.exp (lam * ((S.filter (fun e => f e = true)).card : ℝ)) =
      (1 - p + p * Real.exp lam) ^ S.card := by
  classical
  let w : E → Bool → ℝ := fun e x =>
    if e ∈ S then (if x then p * Real.exp lam else 1 - p)
    else (if x then p else 1 - p)
  have hterm : ∀ f : E → Bool,
      prob p f * Real.exp (lam * ((S.filter (fun e => f e = true)).card : ℝ)) =
        ∏ e : E, w e (f e) := by
    intro f
    have hexp : Real.exp (lam * ((S.filter (fun e => f e = true)).card : ℝ)) =
        ∏ e : E, if e ∈ S ∧ f e = true then Real.exp lam else 1 := by
      have hcard : lam * ((S.filter (fun e => f e = true)).card : ℝ) =
          ∑ e : E, if e ∈ S ∧ f e = true then lam else 0 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 3
        ext e
        simp
      rw [hcard, Real.exp_sum]
      refine Finset.prod_congr rfl fun e _ => ?_
      split_ifs <;> simp
    rw [hexp, prob, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    by_cases he : e ∈ S <;> cases hfe : f e <;> simp [w, he]
  simp only [hterm]
  rw [← Fintype.prod_sum w]
  have h1 : ∀ e : E, ∑ x : Bool, w e x = if e ∈ S then 1 - p + p * Real.exp lam else 1 := by
    intro e
    by_cases he : e ∈ S
    · simp [w, he]; ring
    · simp [w, he]
  simp only [h1, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

private lemma chernoff_two_mu {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset E) :
    ∑ f ∈ Finset.univ.filter (fun f : E → Bool =>
      2 * (p * (S.card : ℝ)) ≤ ((S.filter (fun e => f e = true)).card : ℝ)), prob p f ≤
      Real.exp (-(p * (S.card : ℝ)) / 3) := by
  set μ : ℝ := p * (S.card : ℝ)
  have hμ0 : 0 ≤ μ := by positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmgf := chernoff_mgf p S (Real.log 2)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hmgf
  have h1p : 1 - p + p * 2 = 1 + p := by ring
  rw [h1p] at hmgf
  have hmarkov : Real.exp (Real.log 2 * (2 * μ)) *
      ∑ f ∈ Finset.univ.filter (fun f : E → Bool =>
        2 * μ ≤ ((S.filter (fun e => f e = true)).card : ℝ)), prob p f ≤
      (1 + p) ^ S.card := by
    rw [Finset.mul_sum, ← hmgf]
    calc ∑ f ∈ Finset.univ.filter (fun f : E → Bool =>
            2 * μ ≤ ((S.filter (fun e => f e = true)).card : ℝ)),
          Real.exp (Real.log 2 * (2 * μ)) * prob p f
        ≤ ∑ f ∈ Finset.univ.filter (fun f : E → Bool =>
            2 * μ ≤ ((S.filter (fun e => f e = true)).card : ℝ)),
          prob p f * Real.exp (Real.log 2 * ((S.filter (fun e => f e = true)).card : ℝ)) := by
            refine Finset.sum_le_sum fun f hf => ?_
            rw [mul_comm]
            apply mul_le_mul_of_nonneg_left _ (prob_nonneg hp0 hp1 f)
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hf).2 hlog2_pos.le
      _ ≤ ∑ f : E → Bool,
          prob p f * Real.exp (Real.log 2 * ((S.filter (fun e => f e = true)).card : ℝ)) := by
            refine Finset.sum_le_univ_sum_of_nonneg fun f =>
              mul_nonneg (prob_nonneg hp0 hp1 f) (Real.exp_pos _).le
  have h1p_exp : (1 + p) ^ S.card ≤ Real.exp μ := by
    calc (1 + p) ^ S.card ≤ (Real.exp p) ^ S.card :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp p]) S.card
      _ = Real.exp ((S.card : ℝ) * p) := (Real.exp_nat_mul p S.card).symm
      _ = Real.exp μ := by simp only [μ, mul_comm]
  have hcomb : ∑ f ∈ Finset.univ.filter (fun f : E → Bool =>
      2 * μ ≤ ((S.filter (fun e => f e = true)).card : ℝ)), prob p f ≤
      Real.exp (μ - Real.log 2 * (2 * μ)) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    linarith [hmarkov, h1p_exp]
  refine le_trans hcomb (Real.exp_le_exp.mpr ?_)
  have hlog2_gt : 0.693 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  nlinarith

private def graphOfEdgeBool {n : ℕ} (f : EdgePair n → Bool) : SimpleGraph (Fin n) where
  Adj u v := ∃ h : u ≠ v, f ⟨s(u, v), Sym2.mk_isDiag_iff.not.mpr h⟩ = true
  symm := ⟨fun u v ⟨h, hf⟩ => ⟨h.symm, by simpa [Sym2.eq_swap] using hf⟩⟩
  loopless := ⟨fun u ⟨h, _⟩ => h rfl⟩

private def pairsInFinset {n : ℕ} (S : Finset (Fin n)) : Finset (EdgePair n) :=
  Finset.univ.filter (fun e => ∀ v ∈ e.val, v ∈ S)

private lemma card_pairsInFinset {n : ℕ} (S : Finset (Fin n)) :
    (pairsInFinset S).card = S.card.choose 2 := by
  classical
  have hbij : (pairsInFinset S).card = (S.powersetCard 2).card := by
    refine Finset.card_bij (fun e _ => e.val.toFinset) ?_ ?_ ?_
    · intro e he
      have hmem := (Finset.mem_filter.mp he).2
      rcases e with ⟨e, he_nd⟩
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := Sym2.mk_isDiag_iff.not.mp he_nd
        refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
        · intro x hx
          exact hmem x (Sym2.mem_toFinset.mp hx)
        · simp [Sym2.toFinset_mk_eq, huv]
    · intro e₁ _ e₂ _ heq
      apply Subtype.ext
      rcases e₁ with ⟨e₁, h₁⟩; rcases e₂ with ⟨e₂, h₂⟩
      induction e₁ using Sym2.ind with
      | _ a b =>
        induction e₂ using Sym2.ind with
        | _ c d =>
          have hab : a ≠ b := Sym2.mk_isDiag_iff.not.mp h₁
          have hcd : c ≠ d := Sym2.mk_isDiag_iff.not.mp h₂
          simp only [Sym2.toFinset_mk_eq] at heq
          have ha : a ∈ ({c, d} : Finset (Fin n)) := heq ▸ by simp
          have hb : b ∈ ({c, d} : Finset (Fin n)) := heq ▸ by simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact absurd rfl hab
          · rfl
          · exact Sym2.eq_swap
          · exact absurd rfl hab
    · intro P hP
      obtain ⟨hPS, hPcard⟩ := Finset.mem_powersetCard.mp hP
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hPcard
      refine ⟨⟨s(u, v), Sym2.mk_isDiag_iff.not.mpr huv⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hx => ?_⟩
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> exact hPS (by simp)
      · simp [Sym2.toFinset_mk_eq]
  rw [hbij, Finset.card_powersetCard]

private lemma exists_ramsey_graph (n : ℕ) (hn : 4 ≤ n) :
    ∃ G : SimpleGraph (Fin n),
      IsLocallyRamsey G (Nat.ceil (2 * Real.logb 2 (n : ℝ)) + 2) 2 := by
  classical
  set k := Nat.ceil (2 * Real.logb 2 (n : ℝ)) + 2
  have hn_pos : (0 : ℝ) < n := by positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb_ge2 : (2 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hn_pos]
    norm_num
    exact_mod_cast hn
  have hk_ge6 : 6 ≤ k := by
    have : 4 ≤ Nat.ceil (2 * Real.logb 2 (n : ℝ)) := by
      have : (4 : ℝ) ≤ 2 * Real.logb 2 (n : ℝ) := by linarith
      exact_mod_cast le_trans this (Nat.le_ceil _)
    omega
  -- Bad event: some k-subset is a clique or independent set
  let BadCl (S : Finset (Fin n)) : Finset (EdgePair n → Bool) :=
    Finset.univ.filter (fun f => ∀ e ∈ pairsInFinset S, f e = true)
  let BadInd (S : Finset (Fin n)) : Finset (EdgePair n → Bool) :=
    Finset.univ.filter (fun f => ∀ e ∈ pairsInFinset S, f e = false)
  let AllBad : Finset (EdgePair n → Bool) :=
    ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion (fun S => BadCl S ∪ BadInd S)
  have hbad_lt : ∑ f ∈ AllBad, prob (1 / 2) f < 1 := by
    have h1 : ∑ f ∈ AllBad, prob (1 / 2) f ≤
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (∑ f ∈ BadCl S, prob (1 / 2) f + ∑ f ∈ BadInd S, prob (1 / 2) f) := by
      calc ∑ f ∈ AllBad, prob (1 / 2) f
          ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              ∑ f ∈ BadCl S ∪ BadInd S, prob (1 / 2) f :=
            sum_biUnion_le_of_nonneg (fun f => prob_nonneg (by norm_num) (by norm_num) f)
        _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              (∑ f ∈ BadCl S, prob (1 / 2) f + ∑ f ∈ BadInd S, prob (1 / 2) f) := by
            refine Finset.sum_le_sum fun S _ =>
              sum_union_le_of_nonneg (fun f => prob_nonneg (by norm_num) (by norm_num) f)
    have hterm : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∑ f ∈ BadCl S, prob (1 / 2) f + ∑ f ∈ BadInd S, prob (1 / 2) f =
          2 * (1 / 2 : ℝ) ^ (k.choose 2) := by
      intro S hS
      have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
      have hcl : ∑ f ∈ BadCl S, prob (1 / 2) f = (1 / 2 : ℝ) ^ (k.choose 2) := by
        have := sum_prob_all_eq (1 / 2) (pairsInFinset S) (fun _ => true)
        simpa [BadCl, card_pairsInFinset, hScard] using this
      have hind : ∑ f ∈ BadInd S, prob (1 / 2) f = (1 / 2 : ℝ) ^ (k.choose 2) := by
        have h1 := sum_prob_all_eq (1 / 2) (pairsInFinset S) (fun _ => false)
        simp only [Bool.false_eq_true, ↓reduceIte, Finset.prod_const, card_pairsInFinset, hScard] at h1
        have hsub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
        rw [hsub] at h1
        exact h1
      linarith
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / 2 := by
      have hnat : n.choose k * 2 ≤ n ^ k := by
        have hfac : 2 ≤ k.factorial := by
          calc 2 = Nat.factorial 2 := by decide
            _ ≤ k.factorial := Nat.factorial_le (by omega)
        calc n.choose k * 2 ≤ n.choose k * k.factorial := Nat.mul_le_mul_left _ hfac
          _ = n.descFactorial k := by rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          _ ≤ n ^ k := Nat.descFactorial_le_pow n k
      have hcast : (n.choose k : ℝ) * 2 ≤ (n : ℝ) ^ k := by exact_mod_cast hnat
      linarith
    have h2 : (n.choose k : ℝ) * (2 * (1 / 2 : ℝ) ^ (k.choose 2)) ≤
        (n : ℝ) ^ k * (1 / 2 : ℝ) ^ (k.choose 2) := by
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k.choose 2) := by positivity
      nlinarith
    have h3 : (n : ℝ) ^ k * (1 / 2 : ℝ) ^ (k.choose 2) < 1 := by
      have hn_eq : (n : ℝ) = (2 : ℝ) ^ Real.logb 2 (n : ℝ) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hn_pos).symm
      rw [hn_eq, ← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
        one_div, inv_pow, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_neg (by norm_num),
        ← Real.rpow_add (by norm_num)]
      have hexp_neg : Real.logb 2 (n : ℝ) * (k : ℝ) + -(k.choose 2 : ℝ) < 0 := by
        have hch : (k.choose 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
          rw [Nat.choose_two_right]
          have h2dvd : 2 ∣ k * (k - 1) := Nat.even_mul_pred_self k |>.two_dvd
          have h1 : (k * (k - 1) / 2 : ℕ) * 2 = k * (k - 1) := Nat.div_mul_cancel h2dvd
          have h2 : ((k * (k - 1) / 2 : ℕ) : ℝ) * 2 = (k : ℝ) * ((k : ℝ) - 1) := by
            have hk1 : 1 ≤ k := by omega
            have : ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
              rw [Nat.cast_mul, Nat.cast_sub hk1]; simp
            rw [← this]; exact_mod_cast h1
          linarith
        have hk_lb : 2 * Real.logb 2 (n : ℝ) + 2 ≤ (k : ℝ) := by
          have : 2 * Real.logb 2 (n : ℝ) ≤ (Nat.ceil (2 * Real.logb 2 (n : ℝ)) : ℝ) := Nat.le_ceil _
          have : (k : ℝ) = (Nat.ceil (2 * Real.logb 2 (n : ℝ)) : ℝ) + 2 := by simp [k]
          linarith
        rw [hch]
        have hkpos : (0 : ℝ) < k := by positivity
        nlinarith
      calc (2 : ℝ) ^ (Real.logb 2 (n : ℝ) * (k : ℝ) + -(k.choose 2 : ℝ))
          < (2 : ℝ) ^ (0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp_neg
        _ = 1 := Real.rpow_zero 2
    linarith
  have hex : ∃ f : EdgePair n → Bool, f ∉ AllBad := by
    by_contra hnot
    push Not at hnot
    have huniv : AllBad = Finset.univ := Finset.eq_univ_iff_forall.mpr hnot
    rw [huniv, sum_prob_eq_one] at hbad_lt
    linarith
  obtain ⟨f, hf⟩ := hex
  refine ⟨graphOfEdgeBool f, fun S hScard => ?_⟩
  have hSmem : S ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩
  have hf_not_cl : f ∉ BadCl S := fun h =>
    hf (Finset.mem_biUnion.mpr ⟨S, hSmem, Finset.mem_union_left _ h⟩)
  have hf_not_ind : f ∉ BadInd S := fun h =>
    hf (Finset.mem_biUnion.mpr ⟨S, hSmem, Finset.mem_union_right _ h⟩)
  simp only [BadCl, BadInd, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hf_not_cl hf_not_ind
  constructor
  · obtain ⟨e, heS, hfe⟩ := hf_not_ind
    have hfe_true : f e = true := by cases h : f e <;> simp_all
    rcases e with ⟨e, he_nd⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := Sym2.mk_isDiag_iff.not.mp he_nd
      have huS : u ∈ S := (Finset.mem_filter.mp heS).2 u (Sym2.mem_mk_left u v)
      have hvS : v ∈ S := (Finset.mem_filter.mp heS).2 v (Sym2.mem_mk_right u v)
      refine ⟨{u, v}, Finset.insert_subset_iff.mpr ⟨huS, Finset.singleton_subset_iff.mpr hvS⟩,
        by rw [Finset.card_pair huv], ?_⟩
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact ⟨huv, hfe_true⟩
      · exact ⟨huv.symm, by simpa [Sym2.eq_swap] using hfe_true⟩
      · exact absurd rfl hxy
  · obtain ⟨e, heS, hfe⟩ := hf_not_cl
    have hfe_false : f e = false := by cases h : f e <;> simp_all
    rcases e with ⟨e, he_nd⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := Sym2.mk_isDiag_iff.not.mp he_nd
      have huS : u ∈ S := (Finset.mem_filter.mp heS).2 u (Sym2.mem_mk_left u v)
      have hvS : v ∈ S := (Finset.mem_filter.mp heS).2 v (Sym2.mem_mk_right u v)
      refine ⟨{u, v}, Finset.insert_subset_iff.mpr ⟨huS, Finset.singleton_subset_iff.mpr hvS⟩,
        by rw [Finset.card_pair huv], ?_⟩
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · rintro ⟨_, ht⟩; simp [hfe_false] at ht
      · rintro ⟨_, ht⟩
        have ht' : f ⟨s(y, x), he_nd⟩ = true := by simpa [Sym2.eq_swap] using ht
        rw [hfe_false] at ht'; exact Bool.false_ne_true ht'
      · exact absurd rfl hxy

private lemma greedy_indepSet_of_maxDegree {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (D : ℕ) :
    ∀ k : ℕ, ∀ U : Finset V, (∀ v ∈ U, (U.filter (fun w => H.Adj v w)).card ≤ D) →
      k * (D + 1) ≤ U.card + D →
      ∃ I ⊆ U, k ≤ I.card ∧ H.IsIndepSet (I : Set V) := by
  intro k
  induction k with
  | zero =>
    intro U _ _
    exact ⟨∅, Finset.empty_subset _, Nat.zero_le _, by simp⟩
  | succ k ih =>
    intro U hdeg hcard
    have hmul : (k + 1) * (D + 1) = k * (D + 1) + D + 1 := by ring
    have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hUne
    let U' := U.filter (fun w => w ≠ v ∧ ¬ H.Adj v w)
    have hU'sub : U' ⊆ U := Finset.filter_subset _ U
    have hU'card : U.card ≤ U'.card + (D + 1) := by
      have hdel : U \ U' ⊆ insert v (U.filter (fun w => H.Adj v w)) := by
        intro w hw
        obtain ⟨hwU, hwU'⟩ := Finset.mem_sdiff.mp hw
        simp only [U', Finset.mem_filter, not_and, not_not] at hwU'
        by_cases hwf : w = v
        · subst hwf; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hwU, hwU' hwU hwf⟩)
      have h1 : (U \ U').card ≤ D + 1 := by
        calc (U \ U').card ≤ (insert v (U.filter (fun w => H.Adj v w))).card := Finset.card_le_card hdel
          _ ≤ (U.filter (fun w => H.Adj v w)).card + 1 := Finset.card_insert_le _ _
          _ ≤ D + 1 := Nat.add_le_add_right (hdeg v hv) 1
      have h2 := Finset.card_sdiff_add_card_eq_card hU'sub
      omega
    have hdeg' : ∀ w ∈ U', (U'.filter (fun z => H.Adj w z)).card ≤ D := by
      intro w hw
      exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hU'sub)) (hdeg w (hU'sub hw))
    obtain ⟨I, hIU', hIcard, hIind⟩ := ih U' hdeg' (by omega)
    have hvI : v ∉ I := fun h => (Finset.mem_filter.mp (hIU' h)).2.1 rfl
    refine ⟨insert v I, Finset.insert_subset_iff.mpr ⟨hv, hIU'.trans hU'sub⟩,
      by rw [Finset.card_insert_of_notMem hvI]; omega, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact (Finset.mem_filter.mp (hIU' hy)).2.2
    · exact fun hadj => (Finset.mem_filter.mp (hIU' hx)).2.2 hadj.symm
    · exact hIind hx hy hxy

private lemma exists_indepSet_of_few_edges {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (D : ℕ) (hD : 1 ≤ D)
    (hedges : (∑ v ∈ S, (S.filter (fun w => H.Adj v w)).card) ≤ S.card * D / 2) :
    ∃ I ⊆ S, (S.card + 1) / (2 * (D + 1)) ≤ I.card ∧ H.IsIndepSet (I : Set V) := by
  let U := S.filter (fun v => (S.filter (fun w => H.Adj v w)).card ≤ D)
  have hUsub : U ⊆ S := Finset.filter_subset _ S
  have hbad_card : (S \ U).card * (D + 1) ≤ ∑ v ∈ S, (S.filter (fun w => H.Adj v w)).card := by
    calc (S \ U).card * (D + 1)
        = ∑ _v ∈ S \ U, (D + 1) := by simp
      _ ≤ ∑ v ∈ S \ U, (S.filter (fun w => H.Adj v w)).card := by
          refine Finset.sum_le_sum fun v hv => ?_
          have h1 := Finset.mem_sdiff.mp hv
          have h2 : ¬ (S.filter (fun w => H.Adj v w)).card ≤ D := fun hle =>
            h1.2 (Finset.mem_filter.mpr ⟨h1.1, hle⟩)
          omega
      _ ≤ ∑ v ∈ S, (S.filter (fun w => H.Adj v w)).card :=
          Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have hUcard : S.card / 2 ≤ U.card := by
    have hsplit := Finset.card_sdiff_add_card_eq_card hUsub
    have h1 : (S \ U).card * (D + 1) ≤ S.card * D / 2 := le_trans hbad_card hedges
    have hdiv : S.card * D / 2 * 2 ≤ S.card * D := Nat.div_mul_le_self _ 2
    have h1' : (S \ U).card * (D + 1) * 2 ≤ S.card * D := by linarith
    have h2 : (S \ U).card * 2 ≤ S.card := by nlinarith
    omega
  have hdegU : ∀ v ∈ U, (U.filter (fun w => H.Adj v w)).card ≤ D := fun v hv =>
    le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hUsub)) (Finset.mem_filter.mp hv).2
  obtain ⟨I, hIU, hIcard, hIind⟩ := greedy_indepSet_of_maxDegree H D ((S.card + 1) / (2 * (D + 1))) U hdegU (by
    have hdiv : (S.card + 1) / (2 * (D + 1)) * (2 * (D + 1)) ≤ S.card + 1 := Nat.div_mul_le_self _ _
    have : (S.card + 1) / (2 * (D + 1)) * (D + 1) * 2 ≤ S.card + 1 := by linarith
    omega)
  exact ⟨I, hIU.trans hUsub, hIcard, hIind⟩

private def scrambleGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : EdgePair n → Bool) : SimpleGraph (Fin n) where
  Adj u v := ∃ h : u ≠ v,
    (G.Adj u v ∧ f ⟨s(u, v), Sym2.mk_isDiag_iff.not.mpr h⟩ = false) ∨
    (¬ G.Adj u v ∧ f ⟨s(u, v), Sym2.mk_isDiag_iff.not.mpr h⟩ = true)
  symm := ⟨fun u v ⟨h, hc⟩ => ⟨h.symm, by
    rcases hc with ⟨hadj, hf⟩ | ⟨hnadj, hf⟩
    · exact Or.inl ⟨hadj.symm, by simpa [Sym2.eq_swap] using hf⟩
    · exact Or.inr ⟨fun h' => hnadj h'.symm, by simpa [Sym2.eq_swap] using hf⟩⟩⟩
  loopless := ⟨fun u ⟨h, _⟩ => h rfl⟩

private lemma scramble_locally_ramsey {n m r : ℕ} (hn : 16 ≤ n)
    (hr_lb : 256 * Real.logb 2 (n : ℝ) ≤ (r : ℝ))
    (G : SimpleGraph (Fin n)) (hG : IsLocallyRamsey G m r) :
    ∃ G' : SimpleGraph (Fin n),
      IsLocallyRamsey G' (r / 2) 2 ∧
      IsLocallyRamsey G' m (Nat.ceil ((r : ℝ) / (256 * Real.logb 2 (n : ℝ)))) := by
  classical
  have hn_pos : (0 : ℝ) < n := by positivity
  have hlog_ge4 : (4 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hn_pos]
    norm_num
    exact_mod_cast hn
  have hr_ge256 : 256 ≤ r := by
    have : (256 : ℝ) ≤ (r : ℝ) := by linarith
    exact_mod_cast this
  set p : ℝ := 8 * Real.logb 2 (n : ℝ) / (r : ℝ)
  have hp0 : 0 < p := by positivity
  have hp18 : p ≤ 1 / 8 := by
    simp only [p]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hp1 : p ≤ 1 := by linarith
  set k := r / 2
  have hk_ge128 : 128 ≤ k := by omega
  -- Bad event 1: G' has a clique or indep set of size k
  let Bad1Cl (S : Finset (Fin n)) : Finset (EdgePair n → Bool) :=
    Finset.univ.filter (fun f => (scrambleGraph G f).IsClique (S : Set (Fin n)))
  let Bad1Ind (S : Finset (Fin n)) : Finset (EdgePair n → Bool) :=
    Finset.univ.filter (fun f => (scrambleGraph G f).IsIndepSet (S : Set (Fin n)))
  let AllBad1 : Finset (EdgePair n → Bool) :=
    ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion (fun S => Bad1Cl S ∪ Bad1Ind S)
  -- Bad event 2: some r-subset S has ≥ 2*p*choose(r,2) flipped edges
  let Bad2 (S : Finset (Fin n)) : Finset (EdgePair n → Bool) :=
    Finset.univ.filter (fun f =>
      2 * (p * ((pairsInFinset S).card : ℝ)) ≤
        (((pairsInFinset S).filter (fun e => f e = true)).card : ℝ))
  let AllBad2 : Finset (EdgePair n → Bool) :=
    ((Finset.univ : Finset (Fin n)).powersetCard r).biUnion Bad2
  have hlog2_lt : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlogn_eq : Real.log (n : ℝ) = Real.log 2 * Real.logb 2 (n : ℝ) := by
    rw [Real.logb, mul_div_cancel₀ _ (Real.log_pos (by norm_num)).ne']
  -- Bound probability of AllBad1 < 1/2
  have hbad1_lt : ∑ f ∈ AllBad1, prob p f < 1 / 2 := by
    have h1 : ∑ f ∈ AllBad1, prob p f ≤
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (∑ f ∈ Bad1Cl S, prob p f + ∑ f ∈ Bad1Ind S, prob p f) := by
      calc ∑ f ∈ AllBad1, prob p f
          ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              ∑ f ∈ Bad1Cl S ∪ Bad1Ind S, prob p f :=
            sum_biUnion_le_of_nonneg (fun f => prob_nonneg hp0.le hp1 f)
        _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              (∑ f ∈ Bad1Cl S, prob p f + ∑ f ∈ Bad1Ind S, prob p f) :=
            Finset.sum_le_sum fun S _ => sum_union_le_of_nonneg (fun f => prob_nonneg hp0.le hp1 f)
    have hS_bound : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∑ f ∈ Bad1Cl S, prob p f + ∑ f ∈ Bad1Ind S, prob p f ≤
          2 * (1 - p) ^ (k.choose 2) := by
      intro S hS
      have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
      have hcl_sub : Bad1Cl S ⊆ Finset.univ.filter (fun f : EdgePair n → Bool =>
          ∀ e ∈ pairsInFinset S, f e = decide (e.val ∉ G.edgeSet)) := by
        intro f hf
        have hcl := (Finset.mem_filter.mp hf).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e he => ?_⟩
        rcases e with ⟨e, he_nd⟩
        induction e using Sym2.ind with
        | _ u v =>
          have huv : u ≠ v := Sym2.mk_isDiag_iff.not.mp he_nd
          have huS : u ∈ S := (Finset.mem_filter.mp he).2 u (Sym2.mem_mk_left u v)
          have hvS : v ∈ S := (Finset.mem_filter.mp he).2 v (Sym2.mem_mk_right u v)
          have hadj := hcl huS hvS huv
          rcases hadj with ⟨_, ⟨hg, hff⟩ | ⟨hng, hft⟩⟩
          · have hmem : s(u, v) ∈ G.edgeSet := hg
            simp [hmem, hff]
          · have hmem : s(u, v) ∉ G.edgeSet := hng
            simp [hmem, hft]
      have hind_sub : Bad1Ind S ⊆ Finset.univ.filter (fun f : EdgePair n → Bool =>
          ∀ e ∈ pairsInFinset S, f e = decide (e.val ∈ G.edgeSet)) := by
        intro f hf
        have hind := (Finset.mem_filter.mp hf).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e he => ?_⟩
        rcases e with ⟨e, he_nd⟩
        induction e using Sym2.ind with
        | _ u v =>
          have huv : u ≠ v := Sym2.mk_isDiag_iff.not.mp he_nd
          have huS : u ∈ S := (Finset.mem_filter.mp he).2 u (Sym2.mem_mk_left u v)
          have hvS : v ∈ S := (Finset.mem_filter.mp he).2 v (Sym2.mem_mk_right u v)
          have hnadj := hind huS hvS huv
          by_cases hg : G.Adj u v
          · have hft : f ⟨s(u, v), he_nd⟩ = true := by
              cases hfe : f ⟨s(u, v), he_nd⟩
              · exact absurd ⟨huv, Or.inl ⟨hg, hfe⟩⟩ hnadj
              · rfl
            have hmem : s(u, v) ∈ G.edgeSet := hg
            simp [hmem, hft]
          · have hff : f ⟨s(u, v), he_nd⟩ = false := by
              cases hfe : f ⟨s(u, v), he_nd⟩
              · rfl
              · exact absurd ⟨huv, Or.inr ⟨hg, hfe⟩⟩ hnadj
            have hmem : s(u, v) ∉ G.edgeSet := hg
            simp [hmem, hff]
      have hcl_le : ∑ f ∈ Bad1Cl S, prob p f ≤ (1 - p) ^ (k.choose 2) := by
        calc ∑ f ∈ Bad1Cl S, prob p f
            ≤ ∑ f ∈ Finset.univ.filter (fun f : EdgePair n → Bool =>
                ∀ e ∈ pairsInFinset S, f e = decide (e.val ∉ G.edgeSet)), prob p f :=
              Finset.sum_le_sum_of_subset_of_nonneg hcl_sub (fun f _ _ => prob_nonneg hp0.le hp1 f)
          _ = ∏ e ∈ pairsInFinset S, if decide (e.val ∉ G.edgeSet) then p else 1 - p :=
              sum_prob_all_eq p (pairsInFinset S) _
          _ ≤ ∏ _e ∈ pairsInFinset S, (1 - p) := by
              refine Finset.prod_le_prod (fun e _ => by split_ifs <;> linarith) (fun e _ => ?_)
              split_ifs <;> linarith
          _ = (1 - p) ^ (k.choose 2) := by rw [Finset.prod_const, card_pairsInFinset, hScard]
      have hind_le : ∑ f ∈ Bad1Ind S, prob p f ≤ (1 - p) ^ (k.choose 2) := by
        calc ∑ f ∈ Bad1Ind S, prob p f
            ≤ ∑ f ∈ Finset.univ.filter (fun f : EdgePair n → Bool =>
                ∀ e ∈ pairsInFinset S, f e = decide (e.val ∈ G.edgeSet)), prob p f :=
              Finset.sum_le_sum_of_subset_of_nonneg hind_sub (fun f _ _ => prob_nonneg hp0.le hp1 f)
          _ = ∏ e ∈ pairsInFinset S, if decide (e.val ∈ G.edgeSet) then p else 1 - p :=
              sum_prob_all_eq p (pairsInFinset S) _
          _ ≤ ∏ _e ∈ pairsInFinset S, (1 - p) := by
              refine Finset.prod_le_prod (fun e _ => by split_ifs <;> linarith) (fun e _ => ?_)
              split_ifs <;> linarith
          _ = (1 - p) ^ (k.choose 2) := by rw [Finset.prod_const, card_pairsInFinset, hScard]
      linarith
    have h2 : ∑ f ∈ AllBad1, prob p f ≤ (n.choose k : ℝ) * (2 * (1 - p) ^ (k.choose 2)) := by
      calc ∑ f ∈ AllBad1, prob p f
          ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (2 * (1 - p) ^ (k.choose 2)) :=
            le_trans h1 (Finset.sum_le_sum hS_bound)
        _ = (n.choose k : ℝ) * (2 * (1 - p) ^ (k.choose 2)) := by
            rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by
      have hnat : n.choose k ≤ n ^ k := by
        calc n.choose k ≤ n.choose k * k.factorial := Nat.le_mul_of_pos_right _ (Nat.factorial_pos k)
          _ = n.descFactorial k := by rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          _ ≤ n ^ k := Nat.descFactorial_le_pow n k
      exact_mod_cast hnat
    have h1mp : (1 - p) ^ (k.choose 2) ≤ Real.exp (-p * (k.choose 2 : ℝ)) := by
      calc (1 - p) ^ (k.choose 2) ≤ (Real.exp (-p)) ^ (k.choose 2) :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) _
        _ = Real.exp ((k.choose 2 : ℝ) * (-p)) := (Real.exp_nat_mul (-p) _).symm
        _ = Real.exp (-p * (k.choose 2 : ℝ)) := by ring_nf
    have hnk_eq : (n : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (n : ℝ)) := by
      calc (n : ℝ) ^ k = (Real.exp (Real.log (n : ℝ))) ^ k := by rw [Real.exp_log hn_pos]
        _ = Real.exp ((k : ℝ) * Real.log (n : ℝ)) := (Real.exp_nat_mul _ _).symm
    have hexp_neg : (k : ℝ) * Real.log (n : ℝ) + (-p * (k.choose 2 : ℝ)) ≤ -10 := by
      have hch : (k.choose 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
        rw [Nat.choose_two_right]
        have h2dvd : 2 ∣ k * (k - 1) := Nat.even_mul_pred_self k |>.two_dvd
        have h1 : (k * (k - 1) / 2 : ℕ) * 2 = k * (k - 1) := Nat.div_mul_cancel h2dvd
        have h2 : ((k * (k - 1) / 2 : ℕ) : ℝ) * 2 = (k : ℝ) * ((k : ℝ) - 1) := by
          have hk1 : 1 ≤ k := by omega
          have : ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
            rw [Nat.cast_mul, Nat.cast_sub hk1]; simp
          rw [← this]; exact_mod_cast h1
        linarith
      have hkm1 : (r : ℝ) / 3 ≤ (k : ℝ) - 1 := by
        have h1 : (r : ℝ) / 2 - 1 ≤ (k : ℝ) := by
          have : r ≤ 2 * k + 1 := by omega
          have : (r : ℝ) ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast this
          linarith
        have : (256 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge256
        linarith
      have hp_mul : (4 / 3 : ℝ) * (k : ℝ) * Real.logb 2 (n : ℝ) ≤ p * (k.choose 2 : ℝ) := by
        rw [hch]
        have : p * ((k : ℝ) * ((k : ℝ) - 1) / 2) = (k : ℝ) * (p * ((k : ℝ) - 1) / 2) := by ring
        rw [this]
        have hpk : (4 / 3 : ℝ) * Real.logb 2 (n : ℝ) ≤ p * ((k : ℝ) - 1) / 2 := by
          have h1 : p * ((r : ℝ) / 3) / 2 = (4 / 3 : ℝ) * Real.logb 2 (n : ℝ) := by
            simp only [p]
            have hr_ne : (r : ℝ) ≠ 0 := by positivity
            field_simp [hr_ne]
            ring
          rw [← h1]
          have : p * ((r : ℝ) / 3) ≤ p * ((k : ℝ) - 1) := mul_le_mul_of_nonneg_left hkm1 hp0.le
          linarith
        have := mul_le_mul_of_nonneg_left hpk (Nat.cast_nonneg k)
        linarith
      rw [hlogn_eq]
      have hk_r : (128 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge128
      have hlog_ub : Real.log 2 * Real.logb 2 (n : ℝ) < (7 / 10 : ℝ) * Real.logb 2 (n : ℝ) := by nlinarith
      have hk_log : (k : ℝ) * (Real.log 2 * Real.logb 2 (n : ℝ)) <
          (k : ℝ) * ((7 / 10 : ℝ) * Real.logb 2 (n : ℝ)) :=
        mul_lt_mul_of_pos_left hlog_ub (by positivity)
      nlinarith
    have hfinal : (n.choose k : ℝ) * (2 * (1 - p) ^ (k.choose 2)) ≤ 2 * Real.exp (-10) := by
      calc (n.choose k : ℝ) * (2 * (1 - p) ^ (k.choose 2))
          ≤ (n : ℝ) ^ k * (2 * Real.exp (-p * (k.choose 2 : ℝ))) :=
            mul_le_mul hchoose (by linarith) (by positivity) (by positivity)
        _ = 2 * (Real.exp ((k : ℝ) * Real.log (n : ℝ)) * Real.exp (-p * (k.choose 2 : ℝ))) := by
            rw [hnk_eq]; ring
        _ = 2 * Real.exp ((k : ℝ) * Real.log (n : ℝ) + (-p * (k.choose 2 : ℝ))) := by
            rw [← Real.exp_add]
        _ ≤ 2 * Real.exp (-10) := by linarith [Real.exp_le_exp.mpr hexp_neg]
    have hexp10 : 2 * Real.exp (-10) < 1 / 2 := by
      rw [Real.exp_neg]
      have h1 : (4 : ℝ) < Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
      have h2 : (Real.exp 10)⁻¹ < 1 / 4 := by
        rw [inv_lt_comm₀ (Real.exp_pos 10) (by norm_num)]
        norm_num; linarith
      linarith
    linarith
  -- Bound probability of AllBad2 < 1/2
  have hbad2_lt : ∑ f ∈ AllBad2, prob p f < 1 / 2 := by
    have h1 : ∑ f ∈ AllBad2, prob p f ≤
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ f ∈ Bad2 S, prob p f :=
      sum_biUnion_le_of_nonneg (fun f => prob_nonneg hp0.le hp1 f)
    have hS_bound : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        ∑ f ∈ Bad2 S, prob p f ≤ Real.exp (-(p * (r.choose 2 : ℝ)) / 3) := by
      intro S hS
      have hScard : S.card = r := (Finset.mem_powersetCard.mp hS).2
      have := chernoff_two_mu hp0.le hp1 (pairsInFinset S)
      simpa [Bad2, card_pairsInFinset, hScard] using this
    have h2 : ∑ f ∈ AllBad2, prob p f ≤ (n.choose r : ℝ) * Real.exp (-(p * (r.choose 2 : ℝ)) / 3) := by
      calc ∑ f ∈ AllBad2, prob p f
          ≤ ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
              Real.exp (-(p * (r.choose 2 : ℝ)) / 3) := le_trans h1 (Finset.sum_le_sum hS_bound)
        _ = (n.choose r : ℝ) * Real.exp (-(p * (r.choose 2 : ℝ)) / 3) := by
            rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hchoose : (n.choose r : ℝ) ≤ (n : ℝ) ^ r := by
      have hnat : n.choose r ≤ n ^ r := by
        calc n.choose r ≤ n.choose r * r.factorial := Nat.le_mul_of_pos_right _ (Nat.factorial_pos r)
          _ = n.descFactorial r := by rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          _ ≤ n ^ r := Nat.descFactorial_le_pow n r
      exact_mod_cast hnat
    have hnr_eq : (n : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log (n : ℝ)) := by
      calc (n : ℝ) ^ r = (Real.exp (Real.log (n : ℝ))) ^ r := by rw [Real.exp_log hn_pos]
        _ = Real.exp ((r : ℝ) * Real.log (n : ℝ)) := (Real.exp_nat_mul _ _).symm
    have hexp_neg : (r : ℝ) * Real.log (n : ℝ) + -(p * (r.choose 2 : ℝ)) / 3 ≤ -10 := by
      have hch : (r.choose 2 : ℝ) = (r : ℝ) * ((r : ℝ) - 1) / 2 := by
        rw [Nat.choose_two_right]
        have h2dvd : 2 ∣ r * (r - 1) := Nat.even_mul_pred_self r |>.two_dvd
        have h1 : (r * (r - 1) / 2 : ℕ) * 2 = r * (r - 1) := Nat.div_mul_cancel h2dvd
        have h2 : ((r * (r - 1) / 2 : ℕ) : ℝ) * 2 = (r : ℝ) * ((r : ℝ) - 1) := by
          have hr1 : 1 ≤ r := by omega
          have : ((r * (r - 1) : ℕ) : ℝ) = (r : ℝ) * ((r : ℝ) - 1) := by
            rw [Nat.cast_mul, Nat.cast_sub hr1]; simp
          rw [← this]; exact_mod_cast h1
        linarith
      have hp_eq : p * (r.choose 2 : ℝ) = 4 * ((r : ℝ) - 1) * Real.logb 2 (n : ℝ) := by
        rw [hch]; simp only [p]
        have hr_ne : (r : ℝ) ≠ 0 := by positivity
        field_simp [hr_ne]; ring
      rw [hp_eq, hlogn_eq]
      have hr_r : (256 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge256
      have hlog_ub : Real.log 2 * Real.logb 2 (n : ℝ) < (7 / 10 : ℝ) * Real.logb 2 (n : ℝ) := by nlinarith
      have hr_log : (r : ℝ) * (Real.log 2 * Real.logb 2 (n : ℝ)) <
          (r : ℝ) * ((7 / 10 : ℝ) * Real.logb 2 (n : ℝ)) :=
        mul_lt_mul_of_pos_left hlog_ub (by positivity)
      nlinarith
    have hfinal : (n.choose r : ℝ) * Real.exp (-(p * (r.choose 2 : ℝ)) / 3) ≤ Real.exp (-10) := by
      calc (n.choose r : ℝ) * Real.exp (-(p * (r.choose 2 : ℝ)) / 3)
          ≤ Real.exp ((r : ℝ) * Real.log (n : ℝ)) * Real.exp (-(p * (r.choose 2 : ℝ)) / 3) := by
            rw [← hnr_eq]; exact mul_le_mul_of_nonneg_right hchoose (Real.exp_pos _).le
        _ = Real.exp ((r : ℝ) * Real.log (n : ℝ) + -(p * (r.choose 2 : ℝ)) / 3) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-10) := Real.exp_le_exp.mpr hexp_neg
    have hexp10 : Real.exp (-10) < 1 / 2 := by
      rw [Real.exp_neg]
      have h1 : (2 : ℝ) < Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
      rw [inv_lt_comm₀ (Real.exp_pos 10) (by norm_num)]
      norm_num; linarith
    linarith
  -- Pick f avoiding AllBad1 ∪ AllBad2
  have hex : ∃ f : EdgePair n → Bool, f ∉ AllBad1 ∧ f ∉ AllBad2 := by
    by_contra hnot
    push Not at hnot
    have huniv : AllBad1 ∪ AllBad2 = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun f => by
      by_cases h1 : f ∈ AllBad1
      · exact Finset.mem_union_left _ h1
      · exact Finset.mem_union_right _ (hnot f h1))
    have hsum := sum_union_le_of_nonneg (s := AllBad1) (t := AllBad2) (g := prob p)
      (fun f => prob_nonneg hp0.le hp1 f)
    rw [huniv, sum_prob_eq_one] at hsum
    linarith
  obtain ⟨f, hf1, hf2⟩ := hex
  refine ⟨scrambleGraph G f, ?_, ?_⟩
  · -- Part A: (r/2, 2)-locally Ramsey
    intro S hScard
    have hSmem : S ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩
    have hnot_cl : ¬ (scrambleGraph G f).IsClique (S : Set (Fin n)) := fun h =>
      hf1 (Finset.mem_biUnion.mpr ⟨S, hSmem, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩)
    have hnot_ind : ¬ (scrambleGraph G f).IsIndepSet (S : Set (Fin n)) := fun h =>
      hf1 (Finset.mem_biUnion.mpr ⟨S, hSmem, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩)
    constructor
    · -- Since S is not an independent set, it has an edge!
      simp only [SimpleGraph.isIndepSet_iff, Set.Pairwise, Finset.mem_coe, not_forall, not_not] at hnot_ind
      obtain ⟨u, huS, v, hvS, huv, hadj⟩ := hnot_ind
      refine ⟨{u, v}, Finset.insert_subset_iff.mpr ⟨huS, Finset.singleton_subset_iff.mpr hvS⟩,
        by rw [Finset.card_pair huv], ?_⟩
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hxy
    · -- Since S is not a clique, it has a non-edge!
      simp only [SimpleGraph.isClique_iff, Set.Pairwise, Finset.mem_coe, not_forall] at hnot_cl
      obtain ⟨u, huS, v, hvS, huv, hnadj⟩ := hnot_cl
      refine ⟨{u, v}, Finset.insert_subset_iff.mpr ⟨huS, Finset.singleton_subset_iff.mpr hvS⟩,
        by rw [Finset.card_pair huv], ?_⟩
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hnadj
      · exact fun h => hnadj h.symm
      · exact absurd rfl hxy
  · -- Part B: (m, ceil(r / (256 log₂ n)))-locally Ramsey
    intro S hScard
    obtain ⟨⟨C, hCS, hCr, hCcl⟩, ⟨I, hIS, hIr, hIind⟩⟩ := hG S hScard
    have hclean : ∀ Q : Finset (Fin n), Q.card = r →
        ∃ Q' ⊆ Q, Nat.ceil ((r : ℝ) / (256 * Real.logb 2 (n : ℝ))) ≤ Q'.card ∧
          ∀ u ∈ Q', ∀ v ∈ Q', (huv : u ≠ v) →
            f ⟨s(u, v), Sym2.mk_isDiag_iff.not.mpr huv⟩ = false := by
      intro Q hQcard
      have hQmem : Q ∈ (Finset.univ : Finset (Fin n)).powersetCard r :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hQcard⟩
      have hnot2 : f ∉ Bad2 Q := fun h => hf2 (Finset.mem_biUnion.mpr ⟨Q, hQmem, h⟩)
      simp only [Bad2, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot2
      let Hflip : SimpleGraph (Fin n) := graphOfEdgeBool f
      let D : ℕ := Nat.ceil (32 * Real.logb 2 (n : ℝ))
      have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
      have hdeg_sum : ∑ u ∈ Q, (Q.filter (fun v => Hflip.Adj u v)).card =
          2 * ((pairsInFinset Q).filter (fun e => f e = true)).card := by
        have hlhs : ∑ u ∈ Q, (Q.filter (fun v => Hflip.Adj u v)).card =
            (Q.offDiag.filter (fun uv => Hflip.Adj uv.1 uv.2)).card := by
          have h1 : ∑ u ∈ Q, (Q.filter (fun v => Hflip.Adj u v)).card =
              ∑ u ∈ Q, ((Q.filter (fun v => Hflip.Adj u v)).image (fun v => (u, v))).card := by
            refine Finset.sum_congr rfl fun u _ => (Finset.card_image_of_injective _ ?_).symm
            intro a b h; exact (Prod.mk.inj h).2
          rw [h1, ← Finset.card_biUnion]
          · congr 1
            ext ⟨u, v⟩
            simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_offDiag]
            constructor
            · rintro ⟨u', hu', v', ⟨hv', hadj⟩, hEq⟩
              rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
              exact ⟨⟨hu', hv', hadj.ne⟩, hadj⟩
            · rintro ⟨⟨hu, hv, _⟩, hadj⟩
              exact ⟨u, hu, v, ⟨hv, hadj⟩, rfl⟩
          · intro u₁ _ u₂ _ hne
            rw [Function.onFun, Finset.disjoint_left]
            intro x hx₁ hx₂
            simp only [Finset.mem_image] at hx₁ hx₂
            obtain ⟨_, _, rfl⟩ := hx₁
            obtain ⟨_, _, heq⟩ := hx₂
            exact hne (congrArg Prod.fst heq).symm
        have hfib : (Q.offDiag.filter (fun uv => Hflip.Adj uv.1 uv.2)).card =
            ∑ _e ∈ (pairsInFinset Q).filter (fun e => f e = true), 2 := by
          let v0 : Fin n := ⟨0, by omega⟩
          let v1 : Fin n := ⟨1, by omega⟩
          have h01 : v0 ≠ v1 := by
            intro h
            have : (0 : ℕ) = 1 := congrArg Fin.val h
            omega
          let g : Fin n × Fin n → EdgePair n := fun uv =>
            if h : uv.1 ≠ uv.2 then ⟨s(uv.1, uv.2), Sym2.mk_isDiag_iff.not.mpr h⟩
            else ⟨s(v0, v1), Sym2.mk_isDiag_iff.not.mpr h01⟩
          rw [Finset.card_eq_sum_card_fiberwise (f := g)
            (t := (pairsInFinset Q).filter (fun e => f e = true))]
          · refine Finset.sum_congr rfl fun e he => ?_
            rcases e with ⟨e, he_nd⟩
            induction e using Sym2.ind with
            | _ u v =>
              have huv : u ≠ v := Sym2.mk_isDiag_iff.not.mp he_nd
              have heQ := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
              have hfe : f ⟨s(u, v), he_nd⟩ = true := (Finset.mem_filter.mp he).2
              have huQ : u ∈ Q := heQ u (Sym2.mem_mk_left u v)
              have hvQ : v ∈ Q := heQ v (Sym2.mem_mk_right u v)
              have hfib_eq : (Q.offDiag.filter (fun uv => Hflip.Adj uv.1 uv.2)).filter
                  (fun uv => g uv = ⟨s(u, v), he_nd⟩) = {(u, v), (v, u)} := by
                ext ⟨a, b⟩
                simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert,
                  Finset.mem_singleton, Prod.mk.injEq, g]
                constructor
                · rintro ⟨⟨⟨_, _, hab⟩, _⟩, heq⟩
                  simp only [dif_pos hab, Subtype.mk.injEq, Sym2.eq_iff] at heq
                  exact heq
                · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                  · exact ⟨⟨⟨huQ, hvQ, huv⟩, ⟨huv, hfe⟩⟩, by simp [huv]⟩
                  · exact ⟨⟨⟨hvQ, huQ, huv.symm⟩, ⟨huv.symm, by simpa [Sym2.eq_swap] using hfe⟩⟩,
                      by simp [huv.symm, Sym2.eq_swap]⟩
              rw [hfib_eq, Finset.card_pair (fun h => huv (congrArg Prod.fst h))]
          · intro ⟨u, v⟩ huv
            obtain ⟨huv_od, hadj⟩ := Finset.mem_filter.mp huv
            obtain ⟨huQ, hvQ, hne⟩ := Finset.mem_offDiag.mp huv_od
            simp only [g, dif_pos hne]
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hx => ?_⟩, hadj.2⟩
            rw [Sym2.mem_iff] at hx
            rcases hx with rfl | rfl <;> assumption
        rw [hlhs, hfib, Finset.sum_const, smul_eq_mul, mul_comm]
      have hedges_le : ∑ u ∈ Q, (Q.filter (fun v => Hflip.Adj u v)).card ≤ Q.card * D / 2 := by
        have h1 : ((∑ u ∈ Q, (Q.filter (fun v => Hflip.Adj u v)).card : ℕ) : ℝ) <
            4 * (p * (r.choose 2 : ℝ)) := by
          rw [hdeg_sum, Nat.cast_mul, Nat.cast_ofNat]
          rw [card_pairsInFinset, hQcard] at hnot2
          linarith
        have hch : (r.choose 2 : ℝ) = (r : ℝ) * ((r : ℝ) - 1) / 2 := by
          rw [Nat.choose_two_right]
          have h2dvd : 2 ∣ r * (r - 1) := Nat.even_mul_pred_self r |>.two_dvd
          have h1' : (r * (r - 1) / 2 : ℕ) * 2 = r * (r - 1) := Nat.div_mul_cancel h2dvd
          have h2' : ((r * (r - 1) / 2 : ℕ) : ℝ) * 2 = (r : ℝ) * ((r : ℝ) - 1) := by
            have hr1 : 1 ≤ r := by omega
            have : ((r * (r - 1) : ℕ) : ℝ) = (r : ℝ) * ((r : ℝ) - 1) := by
              rw [Nat.cast_mul, Nat.cast_sub hr1]; simp
            rw [← this]; exact_mod_cast h1'
          linarith
        have h4p : 4 * (p * (r.choose 2 : ℝ)) = 16 * ((r : ℝ) - 1) * Real.logb 2 (n : ℝ) := by
          rw [hch]; simp only [p]; have hr_ne : (r : ℝ) ≠ 0 := by positivity
          field_simp [hr_ne]; ring
        have hD_lb : 32 * Real.logb 2 (n : ℝ) ≤ (D : ℝ) := Nat.le_ceil _
        have h2 : ((∑ u ∈ Q, (Q.filter (fun v => Hflip.Adj u v)).card : ℕ) : ℝ) * 2 ≤ (Q.card : ℝ) * (D : ℝ) := by
          rw [hQcard]
          nlinarith
        have h2nat : (∑ u ∈ Q, (Q.filter (fun v => Hflip.Adj u v)).card) * 2 ≤ Q.card * D := by
          exact_mod_cast h2
        omega
      obtain ⟨Q', hQ'Q, hQ'card, hQ'ind⟩ := exists_indepSet_of_few_edges Hflip Q D hD1 hedges_le
      have hceil_le : Nat.ceil ((r : ℝ) / (256 * Real.logb 2 (n : ℝ))) ≤ (Q.card + 1) / (2 * (D + 1)) := by
        rw [hQcard]
        have hD_ub : (D : ℝ) < 32 * Real.logb 2 (n : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
        have h2D1 : (2 * (D + 1) : ℝ) ≤ 65 * Real.logb 2 (n : ℝ) := by
          have : (2 * (D + 1) : ℝ) = 2 * (D : ℝ) + 2 := by ring
          linarith
        set c := Nat.ceil ((r : ℝ) / (256 * Real.logb 2 (n : ℝ)))
        have hc_lt : (c : ℝ) < (r : ℝ) / (256 * Real.logb 2 (n : ℝ)) + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        have hmul_le : (c : ℝ) * (2 * (D + 1) : ℝ) ≤ (r : ℝ) + 1 := by
          have h1 : ((r : ℝ) / (256 * Real.logb 2 (n : ℝ)) + 1) * (65 * Real.logb 2 (n : ℝ)) ≤ (r : ℝ) + 1 := by
            have hdiv : (r : ℝ) / (256 * Real.logb 2 (n : ℝ)) * (65 * Real.logb 2 (n : ℝ)) =
                (65 / 256 : ℝ) * (r : ℝ) := by
              have hne : Real.logb 2 (n : ℝ) ≠ 0 := by linarith
              field_simp [hne]
            nlinarith
          have h2 : (c : ℝ) * (2 * (D + 1) : ℝ) ≤
              ((r : ℝ) / (256 * Real.logb 2 (n : ℝ)) + 1) * (65 * Real.logb 2 (n : ℝ)) := by
            exact mul_le_mul hc_lt.le h2D1 (by positivity) (by positivity)
          linarith
        have hmul_nat : c * (2 * (D + 1)) ≤ r + 1 := by exact_mod_cast hmul_le
        exact (Nat.le_div_iff_mul_le (by omega)).mpr hmul_nat
      refine ⟨Q', hQ'Q, le_trans hceil_le hQ'card, fun u hu v hv huv => ?_⟩
      cases hfe : f ⟨s(u, v), Sym2.mk_isDiag_iff.not.mpr huv⟩
      · rfl
      · exact absurd ⟨huv, hfe⟩ (hQ'ind hu hv huv)
    obtain ⟨C₀, hC₀C, hC₀card⟩ := Finset.exists_subset_card_eq hCr
    obtain ⟨I₀, hI₀I, hI₀card⟩ := Finset.exists_subset_card_eq hIr
    obtain ⟨C', hC'C₀, hC'card, hC'f⟩ := hclean C₀ hC₀card
    obtain ⟨I', hI'I₀, hI'card, hI'f⟩ := hclean I₀ hI₀card
    refine ⟨⟨C', hC'C₀.trans (hC₀C.trans hCS), hC'card, ?_⟩,
      ⟨I', hI'I₀.trans (hI₀I.trans hIS), hI'card, ?_⟩⟩
    · intro u hu v hv huv
      exact ⟨huv, Or.inl ⟨hCcl (hC₀C (hC'C₀ hu)) (hC₀C (hC'C₀ hv)) huv, hC'f u hu v hv huv⟩⟩
    · intro u hu v hv huv
      rintro ⟨_, ⟨hg, _⟩ | ⟨_, hft⟩⟩
      · exact hIind (hI₀I (hI'I₀ hu)) (hI₀I (hI'I₀ hv)) huv hg
      · rw [hI'f u hu v hv huv] at hft; exact Bool.false_ne_true hft

-- ### Part 2: Lexicographic Power and Lemma 6 (Cases A and B)

private def lexPow {n : ℕ} (G : SimpleGraph (Fin n)) : (ℓ : ℕ) → SimpleGraph (Fin ℓ → Fin n)
  | 0 => ⊥
  | ℓ + 1 =>
    { Adj := fun x y =>
        G.Adj (x 0) (y 0) ∨ (x 0 = y 0 ∧ (lexPow G ℓ).Adj (Fin.tail x) (Fin.tail y))
      symm := ⟨fun x y h => by
        rcases h with h | ⟨heq, htail⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨heq.symm, (lexPow G ℓ).symm.symm _ _ htail⟩⟩
      loopless := ⟨fun x h => by
        rcases h with h | ⟨_, htail⟩
        · exact G.loopless.irrefl _ h
        · exact (lexPow G ℓ).loopless.irrefl _ htail⟩ }

private abbrev lexCons {n ℓ : ℕ} (v : Fin n) (a : Fin ℓ → Fin n) : Fin (ℓ + 1) → Fin n :=
  Fin.cons v a

private def lexFiber {n ℓ : ℕ} (S : Finset (Fin (ℓ + 1) → Fin n)) (v : Fin n) :
    Finset (Fin ℓ → Fin n) :=
  (S.filter (fun x => x 0 = v)).image Fin.tail

private lemma card_lexFiber {n ℓ : ℕ} (S : Finset (Fin (ℓ + 1) → Fin n)) (v : Fin n) :
    (lexFiber S v).card = (S.filter (fun x => x 0 = v)).card := by
  unfold lexFiber
  refine Finset.card_image_of_injOn fun x hx y hy htail => ?_
  have hx0 : x 0 = v := (Finset.mem_filter.mp hx).2
  have hy0 : y 0 = v := (Finset.mem_filter.mp hy).2
  funext i
  refine Fin.cases ?_ ?_ i
  · exact hx0.trans hy0.symm
  · intro j; exact congrFun htail j

private lemma sum_card_lexFiber {n ℓ : ℕ} (S : Finset (Fin (ℓ + 1) → Fin n)) :
    ∑ v : Fin n, (lexFiber S v).card = S.card := by
  simp_rw [card_lexFiber]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (ℓ + 1) → Fin n => x 0)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

private lemma cons_mem_of_mem_lexFiber {n ℓ : ℕ} {S : Finset (Fin (ℓ + 1) → Fin n)}
    {v : Fin n} {a : Fin ℓ → Fin n} (ha : a ∈ lexFiber S v) :
    lexCons v a ∈ S := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
  have hEq : lexCons v (Fin.tail x) = x := by
    rw [lexCons, ← hx0, Fin.cons_self_tail]
  rwa [hEq]

private lemma lexPow_lift_fiber {n ℓ : ℕ} (G : SimpleGraph (Fin n))
    {S : Finset (Fin (ℓ + 1) → Fin n)} {v : Fin n}
    {Q : Finset (Fin ℓ → Fin n)} (hQ : Q ⊆ lexFiber S v) :
    (Q.image (lexCons v)) ⊆ S ∧ (Q.image (lexCons v)).card = Q.card ∧
      ((lexPow G ℓ).IsClique (Q : Set (Fin ℓ → Fin n)) →
        (lexPow G (ℓ + 1)).IsClique ((Q.image (lexCons v)) : Set (Fin (ℓ + 1) → Fin n))) ∧
      ((lexPow G ℓ).IsIndepSet (Q : Set (Fin ℓ → Fin n)) →
        (lexPow G (ℓ + 1)).IsIndepSet ((Q.image (lexCons v)) : Set (Fin (ℓ + 1) → Fin n))) := by
  have hinj : Function.Injective (lexCons v : (Fin ℓ → Fin n) → (Fin (ℓ + 1) → Fin n)) := by
    intro a b h
    simpa [lexCons, Fin.tail_cons] using congrArg Fin.tail h
  refine ⟨?_, Finset.card_image_of_injective Q hinj, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact cons_mem_of_mem_lexFiber (hQ ha)
  · intro hcl x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    have hab : a ≠ b := fun h => hxy (congrArg (lexCons v) h)
    exact Or.inr ⟨rfl, by simpa [lexCons, Fin.tail_cons] using hcl ha hb hab⟩
  · intro hind x hx y hy hxy hadj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    have hab : a ≠ b := fun h => hxy (congrArg (lexCons v) h)
    rcases hadj with hG | ⟨_, htail⟩
    · simp only [lexCons, Fin.cons_zero] at hG
      exact G.loopless.irrefl v hG
    · exact hind ha hb hab (by simpa [lexCons, Fin.tail_cons] using htail)

private lemma lexPow_lift_biUnion {n ℓ : ℕ} (G : SimpleGraph (Fin n))
    {S : Finset (Fin (ℓ + 1) → Fin n)} {K : Finset (Fin n)}
    (Q : Fin n → Finset (Fin ℓ → Fin n)) (hQ : ∀ v ∈ K, Q v ⊆ lexFiber S v) :
    (K.biUnion (fun v => (Q v).image (lexCons v))) ⊆ S ∧
      (K.biUnion (fun v => (Q v).image (lexCons v))).card = ∑ v ∈ K, (Q v).card ∧
      (G.IsClique (K : Set (Fin n)) →
        (∀ v ∈ K, (lexPow G ℓ).IsClique ((Q v) : Set (Fin ℓ → Fin n))) →
        (lexPow G (ℓ + 1)).IsClique ((K.biUnion (fun v => (Q v).image (lexCons v))) : Set (Fin (ℓ + 1) → Fin n))) ∧
      (G.IsIndepSet (K : Set (Fin n)) →
        (∀ v ∈ K, (lexPow G ℓ).IsIndepSet ((Q v) : Set (Fin ℓ → Fin n))) →
        (lexPow G (ℓ + 1)).IsIndepSet ((K.biUnion (fun v => (Q v).image (lexCons v))) : Set (Fin (ℓ + 1) → Fin n))) := by
  have hsub : K.biUnion (fun v => (Q v).image (lexCons v)) ⊆ S := by
    intro x hx
    obtain ⟨v, hvK, hx'⟩ := Finset.mem_biUnion.mp hx
    exact (lexPow_lift_fiber G (hQ v hvK)).1 hx'
  have hcard : (K.biUnion (fun v => (Q v).image (lexCons v))).card = ∑ v ∈ K, (Q v).card := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun v hv => (lexPow_lift_fiber G (hQ v hv)).2.1
    · intro u _ v _ huv
      rw [Function.onFun, Finset.disjoint_left]
      intro x hxu hxv
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxu
      obtain ⟨b, _, hEq⟩ := Finset.mem_image.mp hxv
      have : u = v := by simpa [lexCons] using congrArg (fun f => f 0) hEq.symm
      exact huv this
  refine ⟨hsub, hcard, ?_, ?_⟩
  · intro hKcl hQcl x hx y hy hxy
    obtain ⟨u, huK, hxu⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
    obtain ⟨v, hvK, hyv⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hyv
    by_cases huv : u = v
    · subst huv
      have hab : a ≠ b := fun h => hxy (congrArg (lexCons u) h)
      exact Or.inr ⟨rfl, by simpa [lexCons, Fin.tail_cons] using hQcl u huK ha hb hab⟩
    · exact Or.inl (by simpa [lexCons] using hKcl huK hvK huv)
  · intro hKind hQind x hx y hy hxy hadj
    obtain ⟨u, huK, hxu⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
    obtain ⟨v, hvK, hyv⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hyv
    rcases hadj with hG | ⟨h0, htail⟩
    · have hG' : G.Adj u v := by simpa [lexCons] using hG
      have huv : u ≠ v := hG'.ne
      exact hKind huK hvK huv hG'
    · have huv : u = v := by simpa [lexCons] using h0
      subst huv
      have hab : a ≠ b := fun h => hxy (congrArg (lexCons u) h)
      exact hQind u huK ha hb hab (by simpa [lexCons, Fin.tail_cons] using htail)

private lemma lexPow_singleton {n ℓ : ℕ} (G : SimpleGraph (Fin n))
    {S : Finset (Fin ℓ → Fin n)} (hS : 1 ≤ S.card) :
    (∃ Cl ⊆ S, 1 ≤ Cl.card ∧ (lexPow G ℓ).IsClique (Cl : Set (Fin ℓ → Fin n))) ∧
    (∃ Ind ⊆ S, 1 ≤ Ind.card ∧ (lexPow G ℓ).IsIndepSet (Ind : Set (Fin ℓ → Fin n))) := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  refine ⟨⟨{x}, Finset.singleton_subset_iff.mpr hx, by simp, by simp⟩,
    ⟨{x}, Finset.singleton_subset_iff.mpr hx, by simp, by simp⟩⟩

private lemma lexPow_caseA {n m₂ : ℕ} (hm₂ : 2 ≤ m₂) (hm₂n : m₂ ≤ n)
    (G : SimpleGraph (Fin n)) (hG : IsLocallyRamsey G m₂ 2) :
    ∀ ℓ : ℕ, ∀ S : Finset (Fin ℓ → Fin n), 1 ≤ S.card →
      (∃ Cl ⊆ S, (2 : ℝ) ^ ((Real.logb 2 (S.card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) /
          Real.logb 2 (2 * (n : ℝ))) ≤ (Cl.card : ℝ) ∧
        (lexPow G ℓ).IsClique (Cl : Set (Fin ℓ → Fin n))) ∧
      (∃ Ind ⊆ S, (2 : ℝ) ^ ((Real.logb 2 (S.card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) /
          Real.logb 2 (2 * (n : ℝ))) ≤ (Ind.card : ℝ) ∧
        (lexPow G ℓ).IsIndepSet (Ind : Set (Fin ℓ → Fin n))) := by
  classical
  have hn_ge2 : 2 ≤ n := le_trans hm₂ hm₂n
  have hC_pos : 0 < Real.logb 2 (2 * (n : ℝ)) := by
    apply Real.logb_pos (by norm_num)
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge2
    linarith
  have hlog_m₂_pos : 0 < Real.logb 2 (2 * (m₂ : ℝ)) := by
    apply Real.logb_pos (by norm_num)
    have : (2 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm₂
    linarith
  intro ℓ
  induction ℓ with
  | zero =>
    intro S hS
    have hS1 : S.card = 1 := by
      have hle : S.card ≤ Fintype.card (Fin 0 → Fin n) := Finset.card_le_univ S
      simp at hle; omega
    obtain ⟨⟨Cl, hClS, hCl1, hCl⟩, ⟨Ind, hIndS, hInd1, hInd⟩⟩ := lexPow_singleton G hS
    have hrhs : (2 : ℝ) ^ ((Real.logb 2 (S.card : ℝ) - ((0 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) /
        Real.logb 2 (2 * (n : ℝ))) = 1 := by
      rw [hS1]; simp
    rw [hrhs]
    exact ⟨⟨Cl, hClS, by exact_mod_cast hCl1, hCl⟩, ⟨Ind, hIndS, by exact_mod_cast hInd1, hInd⟩⟩
  | succ ℓ ih =>
    intro S hS
    set C := Real.logb 2 (2 * (n : ℝ))
    set m := S.card
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    by_cases hexp : (Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C ≤ 0
    · obtain ⟨⟨Cl, hClS, hCl1, hCl⟩, ⟨Ind, hIndS, hInd1, hInd⟩⟩ := lexPow_singleton G hS
      have hle1 : (2 : ℝ) ^ ((Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤ 1 := by
        calc (2 : ℝ) ^ _ ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
          _ = 1 := Real.rpow_zero 2
      exact ⟨⟨Cl, hClS, le_trans hle1 (by exact_mod_cast hCl1), hCl⟩,
        ⟨Ind, hIndS, le_trans hle1 (by exact_mod_cast hInd1), hInd⟩⟩
    · push Not at hexp
      have hnum_pos : 0 < Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ)) := by
        exact (div_pos_iff_of_pos_right hC_pos).mp hexp
      -- Subcase 1: some fiber has size ≥ m / (2 * m₂)
      by_cases hbig : ∃ v : Fin n, (m : ℝ) / (2 * (m₂ : ℝ)) ≤ ((lexFiber S v).card : ℝ)
      · obtain ⟨v, hv⟩ := hbig
        have hfv_pos : 0 < (lexFiber S v).card := by
          have : (0 : ℝ) < ((lexFiber S v).card : ℝ) := lt_of_lt_of_le (by positivity) hv
          exact_mod_cast this
        obtain ⟨⟨Cl, hClf, hClc, hCl⟩, ⟨Ind, hIndf, hIndc, hInd⟩⟩ := ih (lexFiber S v) hfv_pos
        have hexp_le : (Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C ≤
            (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C := by
          apply div_le_div_of_nonneg_right _ hC_pos.le
          have hlog_v : Real.logb 2 (m : ℝ) - Real.logb 2 (2 * (m₂ : ℝ)) ≤
              Real.logb 2 ((lexFiber S v).card : ℝ) := by
            rw [← Real.logb_div hm_pos.ne' (by positivity)]
            exact Real.logb_le_logb_of_le (by norm_num) (by positivity) hv
          push_cast; linarith
        have hrpow_le : (2 : ℝ) ^ ((Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤
            (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
        have hliftCl := lexPow_lift_fiber G hClf
        have hliftInd := lexPow_lift_fiber G hIndf
        refine ⟨⟨Cl.image (lexCons v), hliftCl.1, ?_, hliftCl.2.2.1 hCl⟩,
          ⟨Ind.image (lexCons v), hliftInd.1, ?_, hliftInd.2.2.2 hInd⟩⟩
        · rw [hliftCl.2.1]; exact le_trans hrpow_le hClc
        · rw [hliftInd.2.1]; exact le_trans hrpow_le hIndc
      · -- Subcase 2: all fibers < m / (2 * m₂)
        push Not at hbig
        let A : Finset (Fin n) := Finset.univ.filter (fun v => (m : ℝ) / (2 * (n : ℝ)) ≤ ((lexFiber S v).card : ℝ))
        have hA_card : m₂ ≤ A.card := by
          by_contra hlt
          push Not at hlt
          have hsum_all : (m : ℝ) = ∑ v ∈ A, ((lexFiber S v).card : ℝ) +
              ∑ v ∈ Finset.univ \ A, ((lexFiber S v).card : ℝ) := by
            have h1 := sum_card_lexFiber S
            have h2 : ∑ v : Fin n, ((lexFiber S v).card : ℝ) = (m : ℝ) := by
              rw [← Nat.cast_sum, h1]
            rw [← h2, ← Finset.sum_sdiff (Finset.subset_univ A), add_comm]
          have hsumA : ∑ v ∈ A, ((lexFiber S v).card : ℝ) < (m : ℝ) / 2 := by
            have h1 : ∑ v ∈ A, ((lexFiber S v).card : ℝ) ≤ (A.card : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) := by
              calc ∑ v ∈ A, ((lexFiber S v).card : ℝ)
                  ≤ ∑ _v ∈ A, ((m : ℝ) / (2 * (m₂ : ℝ))) := Finset.sum_le_sum fun v _ => (hbig v).le
                _ = (A.card : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
            have h2 : (A.card : ℝ) < (m₂ : ℝ) := by exact_mod_cast hlt
            have h3 : (A.card : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) < (m₂ : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) :=
              mul_lt_mul_of_pos_right h2 (div_pos hm_pos (by positivity))
            have h4 : (m₂ : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) = (m : ℝ) / 2 := by
              have hne : (m₂ : ℝ) ≠ 0 := by positivity
              field_simp [hne]
            linarith
          have hsumAc : ∑ v ∈ Finset.univ \ A, ((lexFiber S v).card : ℝ) ≤ (m : ℝ) / 2 := by
            have h1 : ∑ v ∈ Finset.univ \ A, ((lexFiber S v).card : ℝ) ≤
                ((Finset.univ \ A).card : ℝ) * ((m : ℝ) / (2 * (n : ℝ))) := by
              calc ∑ v ∈ Finset.univ \ A, ((lexFiber S v).card : ℝ)
                  ≤ ∑ _v ∈ Finset.univ \ A, ((m : ℝ) / (2 * (n : ℝ))) := by
                    refine Finset.sum_le_sum fun v hv => ?_
                    have hnv : v ∉ A := (Finset.mem_sdiff.mp hv).2
                    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnv
                    exact hnv.le
                _ = ((Finset.univ \ A).card : ℝ) * ((m : ℝ) / (2 * (n : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
            have h2 : ((Finset.univ \ A).card : ℝ) ≤ (n : ℝ) := by
              have : (Finset.univ \ A).card ≤ n := by
                calc (Finset.univ \ A).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card Finset.sdiff_subset
                  _ = n := by simp
              exact_mod_cast this
            have h3 : ((Finset.univ \ A).card : ℝ) * ((m : ℝ) / (2 * (n : ℝ))) ≤ (n : ℝ) * ((m : ℝ) / (2 * (n : ℝ))) :=
              mul_le_mul_of_nonneg_right h2 (div_nonneg hm_pos.le (by positivity))
            have h4 : (n : ℝ) * ((m : ℝ) / (2 * (n : ℝ))) = (m : ℝ) / 2 := by
              have hne : (n : ℝ) ≠ 0 := by positivity
              field_simp [hne]
            linarith
          linarith
        obtain ⟨A₀, hA₀A, hA₀card⟩ := Finset.exists_subset_card_eq hA_card
        obtain ⟨⟨Kcl, hKclA₀, hKcl2, hKcl⟩, ⟨Kind, hKindA₀, hKind2, hKind⟩⟩ := hG A₀ hA₀card
        have hstep_exp : ∀ v ∈ A₀,
            (Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C ≤
            1 + (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C := by
          intro v hv
          have hv_lb : (m : ℝ) / (2 * (n : ℝ)) ≤ ((lexFiber S v).card : ℝ) :=
            (Finset.mem_filter.mp (hA₀A hv)).2
          have hlog_v : Real.logb 2 (m : ℝ) - C ≤ Real.logb 2 ((lexFiber S v).card : ℝ) := by
            have : Real.logb 2 ((m : ℝ) / (2 * (n : ℝ))) = Real.logb 2 (m : ℝ) - C :=
              Real.logb_div hm_pos.ne' (by positivity)
            rw [← this]
            exact Real.logb_le_logb_of_le (by norm_num) (by positivity) hv_lb
          rw [show (1 : ℝ) + (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C =
              (C + Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C by
            field_simp [hC_pos.ne']; ring]
          apply div_le_div_of_nonneg_right _ hC_pos.le
          push_cast; linarith
        have hih_v : ∀ v ∈ A₀,
            (∃ Cl ⊆ lexFiber S v,
              (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤ (Cl.card : ℝ) ∧
              (lexPow G ℓ).IsClique (Cl : Set (Fin ℓ → Fin n))) ∧
            (∃ Ind ⊆ lexFiber S v,
              (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤ (Ind.card : ℝ) ∧
              (lexPow G ℓ).IsIndepSet (Ind : Set (Fin ℓ → Fin n))) := by
          intro v hv
          have hv_lb : (m : ℝ) / (2 * (n : ℝ)) ≤ ((lexFiber S v).card : ℝ) :=
            (Finset.mem_filter.mp (hA₀A hv)).2
          have hfv_pos : 0 < (lexFiber S v).card := by
            have : (0 : ℝ) < ((lexFiber S v).card : ℝ) := lt_of_lt_of_le (by positivity) hv_lb
            exact_mod_cast this
          exact ih (lexFiber S v) hfv_pos
        let Qcl : Fin n → Finset (Fin ℓ → Fin n) := fun v =>
          if hv : v ∈ A₀ then (hih_v v hv).1.choose else ∅
        let Qind : Fin n → Finset (Fin ℓ → Fin n) := fun v =>
          if hv : v ∈ A₀ then (hih_v v hv).2.choose else ∅
        have hliftCl := lexPow_lift_biUnion G Qcl (fun v hv => by
          simp only [Qcl, dif_pos (hKclA₀ hv)]; exact (hih_v v (hKclA₀ hv)).1.choose_spec.1)
        have hliftInd := lexPow_lift_biUnion G Qind (fun v hv => by
          simp only [Qind, dif_pos (hKindA₀ hv)]; exact (hih_v v (hKindA₀ hv)).2.choose_spec.1)
        constructor
        · refine ⟨Kcl.biUnion (fun v => (Qcl v).image (lexCons v)), hliftCl.1, ?_,
            hliftCl.2.2.1 hKcl (fun v hv => by
              simp only [Qcl, dif_pos (hKclA₀ hv)]; exact (hih_v v (hKclA₀ hv)).1.choose_spec.2.2)⟩
          rw [hliftCl.2.1, Nat.cast_sum]
          set target := (2 : ℝ) ^ ((Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C)
          have hterm : ∀ v ∈ Kcl, target / 2 ≤ ((Qcl v).card : ℝ) := by
            intro v hv
            have hvA₀ : v ∈ A₀ := hKclA₀ hv
            simp only [Qcl, dif_pos hvA₀]
            have hspec := (hih_v v hvA₀).1.choose_spec.2.1
            have h1 : target ≤ 2 * (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) := by
              calc target ≤ (2 : ℝ) ^ (1 + (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (hstep_exp v hvA₀)
                _ = 2 * (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) := by
                    rw [Real.rpow_add (by norm_num), Real.rpow_one]
            linarith
          calc target = 2 * (target / 2) := by ring
            _ ≤ (Kcl.card : ℝ) * (target / 2) := by
                have h2 : (2 : ℝ) ≤ (Kcl.card : ℝ) := by exact_mod_cast hKcl2
                have ht0 : 0 ≤ target / 2 := by positivity
                nlinarith
            _ = ∑ _v ∈ Kcl, (target / 2) := by simp
            _ ≤ ∑ v ∈ Kcl, ((Qcl v).card : ℝ) := Finset.sum_le_sum hterm
        · refine ⟨Kind.biUnion (fun v => (Qind v).image (lexCons v)), hliftInd.1, ?_,
            hliftInd.2.2.2 hKind (fun v hv => by
              simp only [Qind, dif_pos (hKindA₀ hv)]; exact (hih_v v (hKindA₀ hv)).2.choose_spec.2.2)⟩
          rw [hliftInd.2.1, Nat.cast_sum]
          set target := (2 : ℝ) ^ ((Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C)
          have hterm : ∀ v ∈ Kind, target / 2 ≤ ((Qind v).card : ℝ) := by
            intro v hv
            have hvA₀ : v ∈ A₀ := hKindA₀ hv
            simp only [Qind, dif_pos hvA₀]
            have hspec := (hih_v v hvA₀).2.choose_spec.2.1
            have h1 : target ≤ 2 * (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) := by
              calc target ≤ (2 : ℝ) ^ (1 + (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (hstep_exp v hvA₀)
                _ = 2 * (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) := by
                    rw [Real.rpow_add (by norm_num), Real.rpow_one]
            linarith
          calc target = 2 * (target / 2) := by ring
            _ ≤ (Kind.card : ℝ) * (target / 2) := by
                have h2 : (2 : ℝ) ≤ (Kind.card : ℝ) := by exact_mod_cast hKind2
                have ht0 : 0 ≤ target / 2 := by positivity
                nlinarith
            _ = ∑ _v ∈ Kind, (target / 2) := by simp
            _ ≤ ∑ v ∈ Kind, ((Qind v).card : ℝ) := Finset.sum_le_sum hterm

private lemma lexPow_caseB {n m₂ m₃ r₃ M : ℕ} (hm₂ : 2 ≤ m₂) (hm₃ : 1 ≤ m₃) (hr₃ : 2 ≤ r₃) (_hM : 2 ≤ M)
    (G : SimpleGraph (Fin n)) (hG₂ : IsLocallyRamsey G m₂ 2) (hG₃ : IsLocallyRamsey G m₃ r₃) :
    let C : ℝ := max (Real.logb 2 (4 * (m₃ : ℝ))) (Real.logb 2 (M : ℝ) / Real.logb 2 (r₃ : ℝ))
    ∀ ℓ : ℕ, ∀ S : Finset (Fin ℓ → Fin n), 1 ≤ S.card → S.card ≤ M →
      (∃ Cl ⊆ S, (2 : ℝ) ^ ((Real.logb 2 (S.card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤ (Cl.card : ℝ) ∧
        (lexPow G ℓ).IsClique (Cl : Set (Fin ℓ → Fin n))) ∧
      (∃ Ind ⊆ S, (2 : ℝ) ^ ((Real.logb 2 (S.card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤ (Ind.card : ℝ) ∧
        (lexPow G ℓ).IsIndepSet (Ind : Set (Fin ℓ → Fin n))) := by
  classical
  intro C
  have hlog4m₃_pos : 0 < Real.logb 2 (4 * (m₃ : ℝ)) := by
    apply Real.logb_pos (by norm_num)
    have : (1 : ℝ) ≤ (m₃ : ℝ) := by exact_mod_cast hm₃
    linarith
  have hC_ge1 : Real.logb 2 (4 * (m₃ : ℝ)) ≤ C := le_max_left _ _
  have hC_ge2 : Real.logb 2 (M : ℝ) / Real.logb 2 (r₃ : ℝ) ≤ C := le_max_right _ _
  have hC_pos : 0 < C := lt_of_lt_of_le hlog4m₃_pos hC_ge1
  have hlogr₃_pos : 0 < Real.logb 2 (r₃ : ℝ) := by
    apply Real.logb_pos (by norm_num)
    have : (2 : ℝ) ≤ (r₃ : ℝ) := by exact_mod_cast hr₃
    linarith
  have hlog_m₂_pos : 0 < Real.logb 2 (2 * (m₂ : ℝ)) := by
    apply Real.logb_pos (by norm_num)
    have : (2 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm₂
    linarith
  intro ℓ
  induction ℓ with
  | zero =>
    intro S hS _
    have hS1 : S.card = 1 := by
      have hle : S.card ≤ Fintype.card (Fin 0 → Fin n) := Finset.card_le_univ S
      simp at hle; omega
    obtain ⟨⟨Cl, hClS, hCl1, hCl⟩, ⟨Ind, hIndS, hInd1, hInd⟩⟩ := lexPow_singleton G hS
    have hrhs : (2 : ℝ) ^ ((Real.logb 2 (S.card : ℝ) - ((0 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) = 1 := by
      rw [hS1]; simp
    rw [hrhs]
    exact ⟨⟨Cl, hClS, by exact_mod_cast hCl1, hCl⟩, ⟨Ind, hIndS, by exact_mod_cast hInd1, hInd⟩⟩
  | succ ℓ ih =>
    intro S hS hSM
    set m := S.card
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hfib_le_M : ∀ v : Fin n, (lexFiber S v).card ≤ M := fun v => by
      have h1 : (lexFiber S v).card ≤ S.card := by
        rw [card_lexFiber]
        exact Finset.card_filter_le _ _
      omega
    by_cases hexp : (Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C ≤ 0
    · obtain ⟨⟨Cl, hClS, hCl1, hCl⟩, ⟨Ind, hIndS, hInd1, hInd⟩⟩ := lexPow_singleton G hS
      have hle1 : (2 : ℝ) ^ ((Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤ 1 := by
        calc (2 : ℝ) ^ _ ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
          _ = 1 := Real.rpow_zero 2
      exact ⟨⟨Cl, hClS, le_trans hle1 (by exact_mod_cast hCl1), hCl⟩,
        ⟨Ind, hIndS, le_trans hle1 (by exact_mod_cast hInd1), hInd⟩⟩
    · push Not at hexp
      -- Subcase 1: some fiber has size ≥ m / (2 * m₂)
      by_cases hbig : ∃ v : Fin n, (m : ℝ) / (2 * (m₂ : ℝ)) ≤ ((lexFiber S v).card : ℝ)
      · obtain ⟨v, hv⟩ := hbig
        have hfv_pos : 0 < (lexFiber S v).card := by
          have : (0 : ℝ) < ((lexFiber S v).card : ℝ) := lt_of_lt_of_le (by positivity) hv
          exact_mod_cast this
        obtain ⟨⟨Cl, hClf, hClc, hCl⟩, ⟨Ind, hIndf, hIndc, hInd⟩⟩ := ih (lexFiber S v) hfv_pos (hfib_le_M v)
        have hexp_le : (Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C ≤
            (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C := by
          apply div_le_div_of_nonneg_right _ hC_pos.le
          have hlog_v : Real.logb 2 (m : ℝ) - Real.logb 2 (2 * (m₂ : ℝ)) ≤
              Real.logb 2 ((lexFiber S v).card : ℝ) := by
            rw [← Real.logb_div hm_pos.ne' (by positivity)]
            exact Real.logb_le_logb_of_le (by norm_num) (by positivity) hv
          push_cast; linarith
        have hrpow_le : (2 : ℝ) ^ ((Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤
            (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
        have hliftCl := lexPow_lift_fiber G hClf
        have hliftInd := lexPow_lift_fiber G hIndf
        refine ⟨⟨Cl.image (lexCons v), hliftCl.1, ?_, hliftCl.2.2.1 hCl⟩,
          ⟨Ind.image (lexCons v), hliftInd.1, ?_, hliftInd.2.2.2 hInd⟩⟩
        · rw [hliftCl.2.1]; exact le_trans hrpow_le hClc
        · rw [hliftInd.2.1]; exact le_trans hrpow_le hIndc
      · push Not at hbig
        let A : Finset (Fin n) := Finset.univ.filter (fun v => (m : ℝ) / (4 * (m₃ : ℝ)) ≤ ((lexFiber S v).card : ℝ))
        -- Subcase 2: at least m₂ fibers have size ≥ m / (4 * m₃)
        by_cases hA_big : m₂ ≤ A.card
        · obtain ⟨A₀, hA₀A, hA₀card⟩ := Finset.exists_subset_card_eq hA_big
          obtain ⟨⟨Kcl, hKclA₀, hKcl2, hKcl⟩, ⟨Kind, hKindA₀, hKind2, hKind⟩⟩ := hG₂ A₀ hA₀card
          have hstep_exp : ∀ v ∈ A₀,
              (Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C ≤
              1 + (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C := by
            intro v hv
            have hv_lb : (m : ℝ) / (4 * (m₃ : ℝ)) ≤ ((lexFiber S v).card : ℝ) :=
              (Finset.mem_filter.mp (hA₀A hv)).2
            have hlog_v : Real.logb 2 (m : ℝ) - Real.logb 2 (4 * (m₃ : ℝ)) ≤
                Real.logb 2 ((lexFiber S v).card : ℝ) := by
              rw [← Real.logb_div hm_pos.ne' (by positivity)]
              exact Real.logb_le_logb_of_le (by norm_num) (by positivity) hv_lb
            rw [show (1 : ℝ) + (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C =
                (C + Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C by
              field_simp [hC_pos.ne']; ring]
            apply div_le_div_of_nonneg_right _ hC_pos.le
            push_cast; linarith
          have hih_v : ∀ v ∈ A₀,
              (∃ Cl ⊆ lexFiber S v,
                (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤ (Cl.card : ℝ) ∧
                (lexPow G ℓ).IsClique (Cl : Set (Fin ℓ → Fin n))) ∧
              (∃ Ind ⊆ lexFiber S v,
                (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤ (Ind.card : ℝ) ∧
                (lexPow G ℓ).IsIndepSet (Ind : Set (Fin ℓ → Fin n))) := by
            intro v hv
            have hv_lb : (m : ℝ) / (4 * (m₃ : ℝ)) ≤ ((lexFiber S v).card : ℝ) :=
              (Finset.mem_filter.mp (hA₀A hv)).2
            have hfv_pos : 0 < (lexFiber S v).card := by
              have : (0 : ℝ) < ((lexFiber S v).card : ℝ) := lt_of_lt_of_le (by positivity) hv_lb
              exact_mod_cast this
            exact ih (lexFiber S v) hfv_pos (hfib_le_M v)
          let Qcl : Fin n → Finset (Fin ℓ → Fin n) := fun v =>
            if hv : v ∈ A₀ then (hih_v v hv).1.choose else ∅
          let Qind : Fin n → Finset (Fin ℓ → Fin n) := fun v =>
            if hv : v ∈ A₀ then (hih_v v hv).2.choose else ∅
          have hliftCl := lexPow_lift_biUnion G Qcl (fun v hv => by
            simp only [Qcl, dif_pos (hKclA₀ hv)]; exact (hih_v v (hKclA₀ hv)).1.choose_spec.1)
          have hliftInd := lexPow_lift_biUnion G Qind (fun v hv => by
            simp only [Qind, dif_pos (hKindA₀ hv)]; exact (hih_v v (hKindA₀ hv)).2.choose_spec.1)
          constructor
          · refine ⟨Kcl.biUnion (fun v => (Qcl v).image (lexCons v)), hliftCl.1, ?_,
              hliftCl.2.2.1 hKcl (fun v hv => by
                simp only [Qcl, dif_pos (hKclA₀ hv)]; exact (hih_v v (hKclA₀ hv)).1.choose_spec.2.2)⟩
            rw [hliftCl.2.1, Nat.cast_sum]
            set target := (2 : ℝ) ^ ((Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C)
            have hterm : ∀ v ∈ Kcl, target / 2 ≤ ((Qcl v).card : ℝ) := by
              intro v hv
              have hvA₀ : v ∈ A₀ := hKclA₀ hv
              simp only [Qcl, dif_pos hvA₀]
              have hspec := (hih_v v hvA₀).1.choose_spec.2.1
              have h1 : target ≤ 2 * (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) := by
                calc target ≤ (2 : ℝ) ^ (1 + (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hstep_exp v hvA₀)
                  _ = 2 * (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) := by
                      rw [Real.rpow_add (by norm_num), Real.rpow_one]
              linarith
            calc target = 2 * (target / 2) := by ring
              _ ≤ (Kcl.card : ℝ) * (target / 2) := by
                  have h2 : (2 : ℝ) ≤ (Kcl.card : ℝ) := by exact_mod_cast hKcl2
                  have ht0 : 0 ≤ target / 2 := by positivity
                  nlinarith
              _ = ∑ _v ∈ Kcl, (target / 2) := by simp
              _ ≤ ∑ v ∈ Kcl, ((Qcl v).card : ℝ) := Finset.sum_le_sum hterm
          · refine ⟨Kind.biUnion (fun v => (Qind v).image (lexCons v)), hliftInd.1, ?_,
              hliftInd.2.2.2 hKind (fun v hv => by
                simp only [Qind, dif_pos (hKindA₀ hv)]; exact (hih_v v (hKindA₀ hv)).2.choose_spec.2.2)⟩
            rw [hliftInd.2.1, Nat.cast_sum]
            set target := (2 : ℝ) ^ ((Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C)
            have hterm : ∀ v ∈ Kind, target / 2 ≤ ((Qind v).card : ℝ) := by
              intro v hv
              have hvA₀ : v ∈ A₀ := hKindA₀ hv
              simp only [Qind, dif_pos hvA₀]
              have hspec := (hih_v v hvA₀).2.choose_spec.2.1
              have h1 : target ≤ 2 * (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) := by
                calc target ≤ (2 : ℝ) ^ (1 + (Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hstep_exp v hvA₀)
                  _ = 2 * (2 : ℝ) ^ ((Real.logb 2 ((lexFiber S v).card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) := by
                      rw [Real.rpow_add (by norm_num), Real.rpow_one]
              linarith
            calc target = 2 * (target / 2) := by ring
              _ ≤ (Kind.card : ℝ) * (target / 2) := by
                  have h2 : (2 : ℝ) ≤ (Kind.card : ℝ) := by exact_mod_cast hKind2
                  have ht0 : 0 ≤ target / 2 := by positivity
                  nlinarith
              _ = ∑ _v ∈ Kind, (target / 2) := by simp
              _ ≤ ∑ v ∈ Kind, ((Qind v).card : ℝ) := Finset.sum_le_sum hterm
        · -- Subcase 3: at least m₃ nonempty fibers -> pick 1 vertex per fiber in r₃-clique / r₃-indep set!
          push Not at hA_big
          let B : Finset (Fin n) := Finset.univ.filter (fun v => 1 ≤ (lexFiber S v).card)
          have hB_card : m₃ ≤ B.card := by
            by_contra hlt
            push Not at hlt
            have hsum_all : (m : ℝ) = ∑ v ∈ A, ((lexFiber S v).card : ℝ) +
                ∑ v ∈ B \ A, ((lexFiber S v).card : ℝ) := by
              have h1 := sum_card_lexFiber S
              have h2 : ∑ v : Fin n, ((lexFiber S v).card : ℝ) = (m : ℝ) := by
                rw [← Nat.cast_sum, h1]
              have hAB : A ⊆ B := by
                intro v hv
                have hlv : (m : ℝ) / (4 * (m₃ : ℝ)) ≤ ((lexFiber S v).card : ℝ) :=
                  (Finset.mem_filter.mp hv).2
                have hpos : 0 < (lexFiber S v).card := by
                  have : (0 : ℝ) < ((lexFiber S v).card : ℝ) := lt_of_lt_of_le (by positivity) hlv
                  exact_mod_cast this
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
              have hzero : ∑ v ∈ Finset.univ \ B, ((lexFiber S v).card : ℝ) = 0 := by
                apply Finset.sum_eq_zero
                intro v hv
                have hnv : v ∉ B := (Finset.mem_sdiff.mp hv).2
                simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnv
                have : (lexFiber S v).card = 0 := by omega
                simp [this]
              rw [← h2, ← Finset.sum_sdiff (Finset.subset_univ B), hzero, zero_add,
                ← Finset.sum_sdiff hAB, add_comm]
            have hsumA : ∑ v ∈ A, ((lexFiber S v).card : ℝ) < (m : ℝ) / 2 := by
              have h1 : ∑ v ∈ A, ((lexFiber S v).card : ℝ) ≤ (A.card : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) := by
                calc ∑ v ∈ A, ((lexFiber S v).card : ℝ)
                    ≤ ∑ _v ∈ A, ((m : ℝ) / (2 * (m₂ : ℝ))) := Finset.sum_le_sum fun v _ => (hbig v).le
                  _ = (A.card : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
              have h2 : (A.card : ℝ) < (m₂ : ℝ) := by exact_mod_cast hA_big
              have h3 : (A.card : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) < (m₂ : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) :=
                mul_lt_mul_of_pos_right h2 (div_pos hm_pos (by positivity))
              have h4 : (m₂ : ℝ) * ((m : ℝ) / (2 * (m₂ : ℝ))) = (m : ℝ) / 2 := by
                have hne : (m₂ : ℝ) ≠ 0 := by positivity
                field_simp [hne]
              linarith
            have hsumBA : ∑ v ∈ B \ A, ((lexFiber S v).card : ℝ) < (m : ℝ) / 4 := by
              have h1 : ∑ v ∈ B \ A, ((lexFiber S v).card : ℝ) ≤ ((B \ A).card : ℝ) * ((m : ℝ) / (4 * (m₃ : ℝ))) := by
                calc ∑ v ∈ B \ A, ((lexFiber S v).card : ℝ)
                    ≤ ∑ _v ∈ B \ A, ((m : ℝ) / (4 * (m₃ : ℝ))) := by
                      refine Finset.sum_le_sum fun v hv => ?_
                      have hnv : v ∉ A := (Finset.mem_sdiff.mp hv).2
                      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnv
                      exact hnv.le
                  _ = ((B \ A).card : ℝ) * ((m : ℝ) / (4 * (m₃ : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
              have h2 : ((B \ A).card : ℝ) < (m₃ : ℝ) := by
                have : (B \ A).card ≤ B.card := Finset.card_le_card Finset.sdiff_subset
                exact_mod_cast lt_of_le_of_lt this hlt
              have h3 : ((B \ A).card : ℝ) * ((m : ℝ) / (4 * (m₃ : ℝ))) < (m₃ : ℝ) * ((m : ℝ) / (4 * (m₃ : ℝ))) :=
                mul_lt_mul_of_pos_right h2 (div_pos hm_pos (by positivity))
              have h4 : (m₃ : ℝ) * ((m : ℝ) / (4 * (m₃ : ℝ))) = (m : ℝ) / 4 := by
                have hne : (m₃ : ℝ) ≠ 0 := by positivity
                field_simp [hne]
              linarith
            linarith
          obtain ⟨B₀, hB₀B, hB₀card⟩ := Finset.exists_subset_card_eq hB_card
          obtain ⟨⟨Kcl, hKclB₀, hKclr₃, hKcl⟩, ⟨Kind, hKindB₀, hKindr₃, hKind⟩⟩ := hG₃ B₀ hB₀card
          have hne_v : ∀ v ∈ B₀, (lexFiber S v).Nonempty := fun v hv =>
            Finset.card_pos.mp (Finset.mem_filter.mp (hB₀B hv)).2
          let Q1 : Fin n → Finset (Fin ℓ → Fin n) := fun v =>
            if hv : v ∈ B₀ then {(hne_v v hv).choose} else ∅
          have hQ1_sub : ∀ v ∈ B₀, Q1 v ⊆ lexFiber S v := fun v hv => by
            simp only [Q1, dif_pos hv, Finset.singleton_subset_iff]
            exact (hne_v v hv).choose_spec
          have hQ1_card : ∀ v ∈ B₀, (Q1 v).card = 1 := fun v hv => by simp [Q1, dif_pos hv]
          have hliftCl := lexPow_lift_biUnion G Q1 (fun v hv => hQ1_sub v (hKclB₀ hv))
          have hliftInd := lexPow_lift_biUnion G Q1 (fun v hv => hQ1_sub v (hKindB₀ hv))
          have hr₃_ge_target : (2 : ℝ) ^ ((Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) ≤
              (r₃ : ℝ) := by
            have hr₃_eq : (r₃ : ℝ) = (2 : ℝ) ^ Real.logb 2 (r₃ : ℝ) :=
              (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
            rw [hr₃_eq]
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have hm_le_M : Real.logb 2 (m : ℝ) ≤ Real.logb 2 (M : ℝ) :=
              Real.logb_le_logb_of_le (by norm_num) hm_pos (by exact_mod_cast hSM)
            have hdiv_le : Real.logb 2 (M : ℝ) / C ≤ Real.logb 2 (r₃ : ℝ) := by
              rw [div_le_iff₀ hC_pos]
              have := (div_le_iff₀ hlogr₃_pos).mp hC_ge2
              linarith
            have hnum_le : (Real.logb 2 (m : ℝ) - ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C ≤
                Real.logb 2 (M : ℝ) / C := by
              apply div_le_div_of_nonneg_right _ hC_pos.le
              have : (0 : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) * Real.logb 2 (2 * (m₂ : ℝ)) := by positivity
              linarith
            linarith
          refine ⟨⟨Kcl.biUnion (fun v => (Q1 v).image (lexCons v)), hliftCl.1, ?_,
              hliftCl.2.2.1 hKcl (fun v hv => by simp [Q1, dif_pos (hKclB₀ hv)])⟩,
            ⟨Kind.biUnion (fun v => (Q1 v).image (lexCons v)), hliftInd.1, ?_,
              hliftInd.2.2.2 hKind (fun v hv => by simp [Q1, dif_pos (hKindB₀ hv)])⟩⟩
          · rw [hliftCl.2.1, Finset.sum_congr rfl (fun v hv => hQ1_card v (hKclB₀ hv)),
              Finset.sum_const, smul_eq_mul, mul_one]
            exact le_trans hr₃_ge_target (by exact_mod_cast hKclr₃)
          · rw [hliftInd.2.1, Finset.sum_congr rfl (fun v hv => hQ1_card v (hKindB₀ hv)),
              Finset.sum_const, smul_eq_mul, mul_one]
            exact le_trans hr₃_ge_target (by exact_mod_cast hKindr₃)

-- ### Part 3: Theorem 8 (Induction on t ≥ 2) and Final Proof

private lemma isLocallyRamsey_bot_of_gt {N m r : ℕ} (h : N < m) :
    IsLocallyRamsey (⊥ : SimpleGraph (Fin N)) m r := by
  intro S hS
  have hle : S.card ≤ N := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  omega

private lemma isLocallyRamsey_mono {N : ℕ} {G : SimpleGraph (Fin N)}
    {m₁ m₂ r₁ r₂ : ℕ} (hG : IsLocallyRamsey G m₁ r₁) (hm : m₁ ≤ m₂) (hr : r₂ ≤ r₁) :
    IsLocallyRamsey G m₂ r₂ := by
  intro S hS
  obtain ⟨S₀, hS₀S, hS₀card⟩ := Finset.exists_subset_card_eq (by omega : m₁ ≤ S.card)
  obtain ⟨⟨C, hCS₀, hCr, hCcl⟩, ⟨I, hIS₀, hIr, hIind⟩⟩ := hG S₀ hS₀card
  exact ⟨⟨C, hCS₀.trans hS₀S, le_trans hr hCr, hCcl⟩,
    ⟨I, hIS₀.trans hS₀S, le_trans hr hIr, hIind⟩⟩

private lemma isLocallyRamsey_comap {V : Type*} [DecidableEq V] {N m r : ℕ}
    (G : SimpleGraph V) (ι : Fin N ↪ V)
    (hG : ∀ S : Finset V, S.card = m →
      (∃ C ⊆ S, r ≤ C.card ∧ G.IsClique (C : Set V)) ∧
      (∃ I ⊆ S, r ≤ I.card ∧ G.IsIndepSet (I : Set V))) :
    IsLocallyRamsey (G.comap ι) m r := by
  classical
  intro S hS
  have hcard : (S.image ι).card = m := by
    rw [Finset.card_image_of_injective S ι.injective, hS]
  obtain ⟨⟨C, hCS, hCr, hCcl⟩, ⟨I, hIS, hIr, hIind⟩⟩ := hG (S.image ι) hcard
  refine ⟨⟨S.filter (fun x => ι x ∈ C), Finset.filter_subset _ S, ?_, ?_⟩,
    ⟨S.filter (fun x => ι x ∈ I), Finset.filter_subset _ S, ?_, ?_⟩⟩
  · have himg : (S.filter (fun x => ι x ∈ C)).image ι = C := by
      ext y; simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hxC⟩, rfl⟩; exact hxC
      · intro hyC
        obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp (hCS hyC)
        exact ⟨x, ⟨hxS, hyC⟩, rfl⟩
    rw [← Finset.card_image_of_injective _ ι.injective, himg]
    exact hCr
  · intro x hx y hy hxy
    exact hCcl (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2 (ι.injective.ne hxy)
  · have himg : (S.filter (fun x => ι x ∈ I)).image ι = I := by
      ext y; simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hxI⟩, rfl⟩; exact hxI
      · intro hyI
        obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp (hIS hyI)
        exact ⟨x, ⟨hxS, hyI⟩, rfl⟩
    rw [← Finset.card_image_of_injective _ ι.injective, himg]
    exact hIr
  · intro x hx y hy hxy hadj
    exact hIind (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2 (ι.injective.ne hxy) hadj

private lemma two_mul_add_three_le_two_pow : ∀ k : ℕ, 4 ≤ k → 2 * k + 3 ≤ 2 ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk4 : k < 4
    · have hk3 : k = 3 := by omega
      subst hk3; decide
    · have := ih (by omega)
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega

private noncomputable def absLogM (N r t : ℕ) : ℝ :=
  (20000 * (t : ℝ)) ^ t * (Real.logb 2 (r : ℝ)) ^ t * (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ))

private lemma absLogM_pos {N r t : ℕ} (hN : 16 ≤ N) (hr : 2 ≤ r) (ht : 2 ≤ t) :
    0 < absLogM N r t := by
  unfold absLogM
  have hlogN : 0 < Real.logb 2 (N : ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < N))
  have hlogr : 0 < Real.logb 2 (r : ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < r))
  have htpos : (0 : ℝ) < (t : ℝ) := by positivity
  have h1 : 0 < (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := Real.rpow_pos_of_pos hlogN _
  positivity

private lemma locally_ramsey_base {N r : ℕ} (hN : 16 ≤ N) (hr : 2 ≤ r)
    (hcond : (2 : ℝ) * (Real.logb 2 (Real.logb 2 (N : ℝ)) + 12) ≤ Real.logb 2 (r : ℝ)) :
    ∃ G : SimpleGraph (Fin N), IsLocallyRamsey G (Nat.ceil ((2 : ℝ) ^ absLogM N r 2)) r := by
  classical
  set M := Nat.ceil ((2 : ℝ) ^ absLogM N r 2)
  by_cases hMN : N < M
  · exact ⟨⊥, isLocallyRamsey_bot_of_gt hMN⟩
  push Not at hMN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hlogN_ge4 : (4 : ℝ) ≤ Real.logb 2 (N : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hN_pos]
    norm_num; exact_mod_cast hN
  have hloglogN_ge2 : (2 : ℝ) ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have hlogr_ge28 : (28 : ℝ) ≤ Real.logb 2 (r : ℝ) := by linarith
  have hM_ge_rpow : (2 : ℝ) ^ absLogM N r 2 ≤ (M : ℝ) := Nat.le_ceil _
  have hM_pos : 1 ≤ M := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ absLogM N r 2 :=
      Real.one_le_rpow (by norm_num) (absLogM_pos hN hr (by norm_num)).le
    have : (1 : ℝ) ≤ (M : ℝ) := le_trans this hM_ge_rpow
    exact_mod_cast this
  have habs_le_logN : absLogM N r 2 ≤ Real.logb 2 (N : ℝ) := by
    rw [← Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (x := absLogM N r 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
      (le_trans hM_ge_rpow (by exact_mod_cast hMN))
  have hlogM_ge : absLogM N r 2 ≤ Real.logb 2 (M : ℝ) := by
    rw [← Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (x := absLogM N r 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _) hM_ge_rpow
  set sN : ℝ := (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / 2)
  have hsN_ge2 : (2 : ℝ) ≤ sN := by
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h4]
    exact Real.rpow_le_rpow (by norm_num) hlogN_ge4 (by norm_num)
  have hsN_sq : sN * sN = Real.logb 2 (N : ℝ) := by
    simp only [sN]
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have habs_eq : absLogM N r 2 = (40000 : ℝ) ^ 2 * (Real.logb 2 (r : ℝ)) ^ 2 * sN := by
    simp only [absLogM, sN]; norm_num
  set ℓ : ℕ := Nat.floor (sN * Real.logb 2 (r : ℝ))
  have hprod_ge56 : (56 : ℝ) ≤ sN * Real.logb 2 (r : ℝ) := by nlinarith
  have hℓ_ge56 : 56 ≤ ℓ := Nat.le_floor hprod_ge56
  have hℓ_le : (ℓ : ℝ) ≤ sN * Real.logb 2 (r : ℝ) := Nat.floor_le (by linarith)
  have hℓ_ge : sN * Real.logb 2 (r : ℝ) / 2 ≤ (ℓ : ℝ) := by
    have := Nat.lt_floor_add_one (sN * Real.logb 2 (r : ℝ))
    linarith
  have hdiv_ge16 : (16 : ℝ) ≤ Real.logb 2 (N : ℝ) / (ℓ : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (40000 : ℝ) ^ 2 * (Real.logb 2 (r : ℝ)) ^ 2 * sN ≤ sN * sN := by
      rw [hsN_sq, ← habs_eq]; exact habs_le_logN
    have h2 : (40000 : ℝ) ^ 2 * (Real.logb 2 (r : ℝ)) ^ 2 ≤ sN := by nlinarith
    have h3 : 16 * (sN * Real.logb 2 (r : ℝ)) ≤ sN * sN := by nlinarith
    rw [hsN_sq] at h3
    nlinarith
  set log_n : ℕ := Nat.ceil (Real.logb 2 (N : ℝ) / (ℓ : ℝ))
  have hlogn_ge16 : 16 ≤ log_n := by
    have : (16 : ℝ) ≤ (log_n : ℝ) := le_trans hdiv_ge16 (Nat.le_ceil _)
    exact_mod_cast this
  set n : ℕ := 2 ^ log_n
  have hn_ge4 : 4 ≤ n := by
    have : 2 ^ 4 ≤ 2 ^ log_n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlogn_eq : Real.logb 2 (n : ℝ) = (log_n : ℝ) := by
    simp only [n, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hlogn_ub : (log_n : ℝ) ≤ 2 * (Real.logb 2 (N : ℝ) / (ℓ : ℝ)) := by
    have h1 : (log_n : ℝ) < Real.logb 2 (N : ℝ) / (ℓ : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hlogn_ub2 : (log_n : ℝ) ≤ 4 * sN / Real.logb 2 (r : ℝ) := by
    have h1 : Real.logb 2 (N : ℝ) / (ℓ : ℝ) ≤ Real.logb 2 (N : ℝ) / (sN * Real.logb 2 (r : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hℓ_ge
    have h2 : Real.logb 2 (N : ℝ) / (sN * Real.logb 2 (r : ℝ) / 2) = 2 * sN / Real.logb 2 (r : ℝ) := by
      rw [← hsN_sq]
      have hsne : sN ≠ 0 := by linarith
      have hrne : Real.logb 2 (r : ℝ) ≠ 0 := by linarith
      field_simp [hsne, hrne]
    have h3 : 2 * (2 * sN / Real.logb 2 (r : ℝ)) = 4 * sN / Real.logb 2 (r : ℝ) := by ring
    linarith
  have hN_le_nl : N ≤ n ^ ℓ := by
    have h1 : Real.logb 2 (N : ℝ) ≤ (ℓ : ℝ) * (log_n : ℝ) := by
      have h2 : Real.logb 2 (N : ℝ) / (ℓ : ℝ) ≤ (log_n : ℝ) := Nat.le_ceil _
      rw [mul_comm]
      exact (div_le_iff₀ (by positivity)).mp h2
    have h2 : (N : ℝ) ≤ (2 : ℝ) ^ ((ℓ : ℝ) * (log_n : ℝ)) := by
      rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hN_pos]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    have h3 : (2 : ℝ) ^ ((ℓ : ℝ) * (log_n : ℝ)) = ((n ^ ℓ : ℕ) : ℝ) := by
      simp only [n, Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_mul, mul_comm, ← Real.rpow_natCast, Nat.cast_mul]
    rw [h3] at h2
    exact_mod_cast h2
  obtain ⟨G, hG⟩ := exists_ramsey_graph n hn_ge4
  set m₂ := Nat.ceil (2 * Real.logb 2 (n : ℝ)) + 2
  have hm₂_ge2 : 2 ≤ m₂ := by omega
  have hm₂_le_n : m₂ ≤ n := by
    have hceil_eq : Nat.ceil (2 * Real.logb 2 (n : ℝ)) = 2 * log_n := by
      rw [hlogn_eq]
      exact_mod_cast Nat.ceil_natCast (2 * log_n)
    have : m₂ = 2 * log_n + 2 := by simp only [m₂, hceil_eq]
    have hpow := two_mul_add_three_le_two_pow log_n (by omega)
    omega
  have hcard_le : Fintype.card (Fin N) ≤ Fintype.card (Fin ℓ → Fin n) := by
    simpa [Fintype.card_fin] using hN_le_nl
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard_le
  refine ⟨(lexPow G ℓ).comap ι, isLocallyRamsey_comap (lexPow G ℓ) ι (fun S hScard => ?_)⟩
  have hS1 : 1 ≤ S.card := by omega
  obtain ⟨⟨Cl, hClS, hClc, hCl⟩, ⟨Ind, hIndS, hIndc, hInd⟩⟩ := lexPow_caseA hm₂_ge2 hm₂_le_n G hG ℓ S hS1
  have hr_le : (r : ℝ) ≤ (2 : ℝ) ^ ((Real.logb 2 (S.card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) /
      Real.logb 2 (2 * (n : ℝ))) := by
    rw [hScard]
    rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hr_pos]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hC_pos : 0 < Real.logb 2 (2 * (n : ℝ)) := by
      apply Real.logb_pos (by norm_num)
      have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge4
      linarith
    have hC_ub : Real.logb 2 (2 * (n : ℝ)) ≤ 8 * sN / Real.logb 2 (r : ℝ) := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num), hlogn_eq]
      have h1 : (1 : ℝ) ≤ (log_n : ℝ) := by exact_mod_cast (by omega : 1 ≤ log_n)
      have h2 : 2 * (4 * sN / Real.logb 2 (r : ℝ)) = 8 * sN / Real.logb 2 (r : ℝ) := by ring
      linarith
    have hm₂_ub : 2 * (m₂ : ℝ) ≤ 8 * Real.logb 2 (N : ℝ) := by
      have hceil_eq : Nat.ceil (2 * Real.logb 2 (n : ℝ)) = 2 * log_n := by
        rw [hlogn_eq]; exact_mod_cast Nat.ceil_natCast (2 * log_n)
      have hm₂_eq : (m₂ : ℝ) = 2 * (log_n : ℝ) + 2 := by
        have : m₂ = 2 * log_n + 2 := by simp only [m₂, hceil_eq]
        exact_mod_cast this
      have hlogn_le_logN : (log_n : ℝ) ≤ Real.logb 2 (N : ℝ) := by
        have : Real.logb 2 (N : ℝ) / (ℓ : ℝ) ≤ Real.logb 2 (N : ℝ) / 56 :=
          div_le_div_of_nonneg_left (by linarith) (by norm_num) (by exact_mod_cast hℓ_ge56)
        linarith
      linarith
    have hlog_m₂_le : Real.logb 2 (2 * (m₂ : ℝ)) ≤ Real.logb 2 (r : ℝ) := by
      have h1 : Real.logb 2 (2 * (m₂ : ℝ)) ≤ Real.logb 2 (8 * Real.logb 2 (N : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hm₂_ub
      have h2 : Real.logb 2 (8 * Real.logb 2 (N : ℝ)) = 3 + Real.logb 2 (Real.logb 2 (N : ℝ)) := by
        rw [Real.logb_mul (by norm_num) (by linarith)]
        have : Real.logb 2 (8 : ℝ) = 3 := by
          rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          ring
        linarith
      linarith
    have hℓ_sub : (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ)) ≤ sN * (Real.logb 2 (r : ℝ)) ^ 2 := by
      have h1 : (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ)) ≤ (sN * Real.logb 2 (r : ℝ)) * Real.logb 2 (r : ℝ) :=
        mul_le_mul hℓ_le hlog_m₂_le (Real.logb_nonneg (by norm_num) (by
          have : (2 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm₂_ge2
          linarith)) (by positivity)
      linarith
    rw [le_div_iff₀ hC_pos]
    have h1 : Real.logb 2 (r : ℝ) * Real.logb 2 (2 * (n : ℝ)) ≤ 8 * sN := by
      have := mul_le_mul_of_nonneg_left hC_ub (by linarith : 0 ≤ Real.logb 2 (r : ℝ))
      have hcancel : Real.logb 2 (r : ℝ) * (8 * sN / Real.logb 2 (r : ℝ)) = 8 * sN := by
        have hrne : Real.logb 2 (r : ℝ) ≠ 0 := by linarith
        field_simp [hrne]
      linarith
    have h2 : (8 : ℝ) * sN + sN * (Real.logb 2 (r : ℝ)) ^ 2 ≤ absLogM N r 2 := by
      rw [habs_eq]
      have hr2 : (1 : ℝ) ≤ (Real.logb 2 (r : ℝ)) ^ 2 := by nlinarith only [hlogr_ge28]
      nlinarith only [hsN_ge2, hr2]
    linarith only [hlogM_ge, hℓ_sub, h1, h2]
  exact ⟨⟨Cl, hClS, by exact_mod_cast le_trans hr_le hClc, hCl⟩,
    ⟨Ind, hIndS, by exact_mod_cast le_trans hr_le hIndc, hInd⟩⟩

private lemma absLogM_step_core {N n r r' t : ℕ} (ht : 2 ≤ t)
    (hlogN_ge4 : (4 : ℝ) ≤ Real.logb 2 (N : ℝ))
    (hlogr_ge42 : (42 : ℝ) ≤ Real.logb 2 (r : ℝ))
    (hlogr'_pos : 0 < Real.logb 2 (r' : ℝ))
    (hlogr'_le : Real.logb 2 (r' : ℝ) ≤ (1 + 4 / (t : ℝ)) * Real.logb 2 (r : ℝ))
    (hlogn_pos : 0 < Real.logb 2 (n : ℝ))
    (habs_pos : 0 < absLogM N r (t + 1))
    (hlogn_ub : Real.logb 2 (n : ℝ) ≤ 8 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ) * Real.logb 2 (N : ℝ) /
      absLogM N r (t + 1)) :
    Real.logb 2 (r : ℝ) * absLogM n r' t ≤ absLogM N r (t + 1) / 4 := by
  have ht_pos : (0 : ℝ) < (t : ℝ) := by positivity
  have ht_ge2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  set A := absLogM N r (t + 1)
  have hA_pos : 0 < A := habs_pos
  suffices hmul : 4 * Real.logb 2 (r : ℝ) * absLogM n r' t * A ^ ((1 : ℝ) / (t : ℝ)) ≤
      A ^ (((t : ℝ) + 1) / (t : ℝ)) by
    have hsplit : A ^ (((t : ℝ) + 1) / (t : ℝ)) = A * A ^ ((1 : ℝ) / (t : ℝ)) := by
      rw [show ((t : ℝ) + 1) / (t : ℝ) = 1 + 1 / (t : ℝ) by field_simp [ht_pos.ne'],
        Real.rpow_add hA_pos, Real.rpow_one]
    rw [hsplit] at hmul
    have hpow_pos : 0 < A ^ ((1 : ℝ) / (t : ℝ)) := Real.rpow_pos_of_pos hA_pos _
    nlinarith only [hmul, hpow_pos]
  have hlogn_rpow : (Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) * A ^ ((1 : ℝ) / (t : ℝ)) ≤
      (8 * ((t : ℝ) + 2)) ^ ((1 : ℝ) / (t : ℝ)) * (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) *
        (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := by
    rw [← Real.mul_rpow hlogn_pos.le hA_pos.le]
    have h1 : Real.logb 2 (n : ℝ) * A ≤
        8 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ) * Real.logb 2 (N : ℝ) := by
      have := mul_le_mul_of_nonneg_right hlogn_ub hA_pos.le
      rwa [div_mul_cancel₀ _ hA_pos.ne'] at this
    calc (Real.logb 2 (n : ℝ) * A) ^ ((1 : ℝ) / (t : ℝ))
        ≤ (8 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ) * Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) :=
          Real.rpow_le_rpow (mul_nonneg hlogn_pos.le hA_pos.le) h1 (by positivity)
      _ = (8 * ((t : ℝ) + 2)) ^ ((1 : ℝ) / (t : ℝ)) * (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) *
            (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := by
          rw [Real.mul_rpow (by positivity) (by linarith),
            Real.mul_rpow (by positivity) hlogr'_pos.le]
  have h8t_rpow : (8 * ((t : ℝ) + 2)) ^ ((1 : ℝ) / (t : ℝ)) ≤ 8 * ((t : ℝ) + 2) := by
    calc (8 * ((t : ℝ) + 2)) ^ ((1 : ℝ) / (t : ℝ))
        ≤ (8 * ((t : ℝ) + 2)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [div_le_one ht_pos]; linarith)
      _ = 8 * ((t : ℝ) + 2) := Real.rpow_one _
  have h14t : (1 + 4 / (t : ℝ)) ^ t * (1 + 4 / (t : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) ≤ 243 := by
    have ha : (1 + 4 / (t : ℝ)) ^ t ≤ 81 := by
      have he3 : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      calc (1 + 4 / (t : ℝ)) ^ t ≤ (Real.exp (4 / (t : ℝ))) ^ t :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (4 / (t : ℝ))]) t
        _ = Real.exp ((t : ℝ) * (4 / (t : ℝ))) := (Real.exp_nat_mul _ t).symm
        _ = Real.exp 4 := by congr 1; field_simp [ht_pos.ne']
        _ = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ (3 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he3 4
        _ = 81 := by norm_num
    have hb : (1 + 4 / (t : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) ≤ 3 := by
      have hge1 : (1 : ℝ) ≤ 1 + 4 / (t : ℝ) := by
        have : (0 : ℝ) ≤ 4 / (t : ℝ) := by positivity
        linarith
      have hle3 : 1 + 4 / (t : ℝ) ≤ 3 := by
        have : 4 / (t : ℝ) ≤ 2 := by rw [div_le_iff₀ ht_pos]; linarith
        linarith
      calc (1 + 4 / (t : ℝ)) ^ ((1 : ℝ) / (t : ℝ))
          ≤ (1 + 4 / (t : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge1 (by rw [div_le_one ht_pos]; linarith)
        _ = 1 + 4 / (t : ℝ) := Real.rpow_one _
        _ ≤ 3 := hle3
    have ha0 : 0 ≤ (1 + 4 / (t : ℝ)) ^ t := by positivity
    have hb0 : 0 ≤ (1 + 4 / (t : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := by positivity
    nlinarith only [ha, hb, ha0, hb0]
  have hlogr'_pow : (Real.logb 2 (r' : ℝ)) ^ t * (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) ≤
      243 * (Real.logb 2 (r : ℝ)) ^ ((t : ℝ) + 1 / (t : ℝ)) := by
    have ha : (Real.logb 2 (r' : ℝ)) ^ t ≤ (1 + 4 / (t : ℝ)) ^ t * (Real.logb 2 (r : ℝ)) ^ t := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hlogr'_pos.le hlogr'_le t
    have hb : (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) ≤
        (1 + 4 / (t : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) * (Real.logb 2 (r : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := by
      rw [← Real.mul_rpow (by positivity) (by linarith)]
      exact Real.rpow_le_rpow hlogr'_pos.le hlogr'_le (by positivity)
    have hc : (Real.logb 2 (r : ℝ)) ^ t * (Real.logb 2 (r : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) =
        (Real.logb 2 (r : ℝ)) ^ ((t : ℝ) + 1 / (t : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    have hmul1 := mul_le_mul ha hb (by positivity) (by positivity)
    have hmul1' : (Real.logb 2 (r' : ℝ)) ^ t * (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) ≤
        ((1 + 4 / (t : ℝ)) ^ t * (1 + 4 / (t : ℝ)) ^ ((1 : ℝ) / (t : ℝ))) *
          ((Real.logb 2 (r : ℝ)) ^ t * (Real.logb 2 (r : ℝ)) ^ ((1 : ℝ) / (t : ℝ))) := by
      linarith only [hmul1]
    calc (Real.logb 2 (r' : ℝ)) ^ t * (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ))
        ≤ ((1 + 4 / (t : ℝ)) ^ t * (1 + 4 / (t : ℝ)) ^ ((1 : ℝ) / (t : ℝ))) *
            ((Real.logb 2 (r : ℝ)) ^ t * (Real.logb 2 (r : ℝ)) ^ ((1 : ℝ) / (t : ℝ))) := hmul1'
      _ ≤ 243 * (Real.logb 2 (r : ℝ)) ^ ((t : ℝ) + 1 / (t : ℝ)) := by
          rw [hc]; exact mul_le_mul_of_nonneg_right h14t (by positivity)
  have hlhs_le : 4 * Real.logb 2 (r : ℝ) * absLogM n r' t * A ^ ((1 : ℝ) / (t : ℝ)) ≤
      (7776 * ((t : ℝ) + 2) * (20000 * (t : ℝ)) ^ t) *
        (Real.logb 2 (r : ℝ)) ^ (1 + (t : ℝ) + 1 / (t : ℝ)) *
        (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := by
    have hrew : 4 * Real.logb 2 (r : ℝ) * absLogM n r' t * A ^ ((1 : ℝ) / (t : ℝ)) =
        4 * (20000 * (t : ℝ)) ^ t * Real.logb 2 (r : ℝ) * (Real.logb 2 (r' : ℝ)) ^ t *
          ((Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) * A ^ ((1 : ℝ) / (t : ℝ))) := by
      unfold absLogM; ring
    rw [hrew]
    have hstep1 : 4 * (20000 * (t : ℝ)) ^ t * Real.logb 2 (r : ℝ) * (Real.logb 2 (r' : ℝ)) ^ t *
          ((Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) * A ^ ((1 : ℝ) / (t : ℝ))) ≤
        4 * (20000 * (t : ℝ)) ^ t * Real.logb 2 (r : ℝ) * (Real.logb 2 (r' : ℝ)) ^ t *
          ((8 * ((t : ℝ) + 2)) ^ ((1 : ℝ) / (t : ℝ)) * (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) *
            (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ))) :=
      mul_le_mul_of_nonneg_left hlogn_rpow (by positivity)
    have hstep2 : 4 * (20000 * (t : ℝ)) ^ t * Real.logb 2 (r : ℝ) * (Real.logb 2 (r' : ℝ)) ^ t *
          ((8 * ((t : ℝ) + 2)) ^ ((1 : ℝ) / (t : ℝ)) * (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) *
            (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ))) =
        4 * (8 * ((t : ℝ) + 2)) ^ ((1 : ℝ) / (t : ℝ)) * (20000 * (t : ℝ)) ^ t *
          Real.logb 2 (r : ℝ) * ((Real.logb 2 (r' : ℝ)) ^ t * (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ))) *
          (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := by ring
    have hstep3 : 4 * (8 * ((t : ℝ) + 2)) ^ ((1 : ℝ) / (t : ℝ)) * (20000 * (t : ℝ)) ^ t *
          Real.logb 2 (r : ℝ) * ((Real.logb 2 (r' : ℝ)) ^ t * (Real.logb 2 (r' : ℝ)) ^ ((1 : ℝ) / (t : ℝ))) *
          (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) ≤
        4 * (8 * ((t : ℝ) + 2)) * (20000 * (t : ℝ)) ^ t *
          Real.logb 2 (r : ℝ) * (243 * (Real.logb 2 (r : ℝ)) ^ ((t : ℝ) + 1 / (t : ℝ))) *
          (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := by
      have ha : 4 * (8 * ((t : ℝ) + 2)) ^ ((1 : ℝ) / (t : ℝ)) * (20000 * (t : ℝ)) ^ t * Real.logb 2 (r : ℝ) ≤
          4 * (8 * ((t : ℝ) + 2)) * (20000 * (t : ℝ)) ^ t * Real.logb 2 (r : ℝ) := by
        have := mul_le_mul_of_nonneg_left h8t_rpow (by norm_num : (0 : ℝ) ≤ 4)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity)) (by linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul ha hlogr'_pow (by positivity) (by positivity)) (by positivity)
    have hr_add : Real.logb 2 (r : ℝ) * (Real.logb 2 (r : ℝ)) ^ ((t : ℝ) + 1 / (t : ℝ)) =
        (Real.logb 2 (r : ℝ)) ^ (1 + (t : ℝ) + 1 / (t : ℝ)) := by
      symm
      rw [add_assoc, Real.rpow_add (by linarith), Real.rpow_one]
    calc _ ≤ _ := hstep1
      _ = _ := hstep2
      _ ≤ _ := hstep3
      _ = (7776 * ((t : ℝ) + 2) * (20000 * (t : ℝ)) ^ t) *
            (Real.logb 2 (r : ℝ) * (Real.logb 2 (r : ℝ)) ^ ((t : ℝ) + 1 / (t : ℝ))) *
            (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := by ring
      _ = _ := by rw [hr_add]
  have hrhs_eq : A ^ (((t : ℝ) + 1) / (t : ℝ)) =
      ((20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1)) ^ (((t : ℝ) + 1) / (t : ℝ)) *
        (Real.logb 2 (r : ℝ)) ^ (((t : ℝ) + 1) ^ 2 / (t : ℝ)) *
        (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / (t : ℝ)) := by
    simp only [A, absLogM]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    · congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      congr 1; push_cast; ring
    · rw [← Real.rpow_mul (by linarith)]
      congr 1
      have hne : ((t + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast; field_simp [ht_pos.ne']
  have hc_le : 7776 * ((t : ℝ) + 2) * (20000 * (t : ℝ)) ^ t ≤
      ((20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1)) ^ (((t : ℝ) + 1) / (t : ℝ)) := by
    have h1 : 7776 * ((t : ℝ) + 2) ≤ 20000 * ((t + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h2 : (20000 * (t : ℝ)) ^ t ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ t :=
      pow_le_pow_left₀ (by positivity) (by push_cast; linarith) t
    have h3 : 7776 * ((t : ℝ) + 2) * (20000 * (t : ℝ)) ^ t ≤
        (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) := by
      rw [pow_succ']
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) ≤
        ((20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1)) ^ (((t : ℝ) + 1) / (t : ℝ)) := by
      calc (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1)
          = ((20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1)) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ((20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1)) ^ (((t : ℝ) + 1) / (t : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le
              (one_le_pow₀ (by push_cast; linarith))
              (by rw [one_le_div ht_pos]; linarith)
    linarith only [h3, h4]
  have hrexp_le : (Real.logb 2 (r : ℝ)) ^ (1 + (t : ℝ) + 1 / (t : ℝ)) ≤
      (Real.logb 2 (r : ℝ)) ^ (((t : ℝ) + 1) ^ 2 / (t : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    rw [le_div_iff₀ ht_pos]
    have h1 : (1 + (t : ℝ) + 1 / (t : ℝ)) * (t : ℝ) = (t : ℝ) + (t : ℝ) ^ 2 + 1 := by
      field_simp [ht_pos.ne']
    rw [h1]; nlinarith only [ht_ge2]
  rw [hrhs_eq]
  exact le_trans hlhs_le (mul_le_mul_of_nonneg_right
    (mul_le_mul hc_le hrexp_le (by positivity) (by positivity)) (by positivity))

set_option maxHeartbeats 800000 in
private lemma locally_ramsey_step {t : ℕ} (ht : 2 ≤ t)
    (ih : ∀ N r : ℕ, 16 ≤ N → 2 ≤ r →
      (t : ℝ) * (Real.logb 2 (Real.logb 2 (N : ℝ)) + 12) ≤ Real.logb 2 (r : ℝ) →
      ∃ G : SimpleGraph (Fin N), IsLocallyRamsey G (Nat.ceil ((2 : ℝ) ^ absLogM N r t)) r) :
    ∀ N r : ℕ, 16 ≤ N → 2 ≤ r →
      ((t + 1 : ℕ) : ℝ) * (Real.logb 2 (Real.logb 2 (N : ℝ)) + 12) ≤ Real.logb 2 (r : ℝ) →
      ∃ G : SimpleGraph (Fin N), IsLocallyRamsey G (Nat.ceil ((2 : ℝ) ^ absLogM N r (t + 1))) r := by
  classical
  intro N r hN hr hcond
  set M := Nat.ceil ((2 : ℝ) ^ absLogM N r (t + 1))
  by_cases hMN : N < M
  · exact ⟨⊥, isLocallyRamsey_bot_of_gt hMN⟩
  push Not at hMN
  have ht_pos : (0 : ℝ) < (t : ℝ) := by positivity
  have ht_ge2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hlogN_ge4 : (4 : ℝ) ≤ Real.logb 2 (N : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hN_pos]
    norm_num; exact_mod_cast hN
  have hloglogN_ge2 : (2 : ℝ) ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have hlogr_ge_t : (t : ℝ) * 14 ≤ Real.logb 2 (r : ℝ) := by
    have : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
    nlinarith
  have hlogr_ge42 : (42 : ℝ) ≤ Real.logb 2 (r : ℝ) := by
    have : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
    nlinarith
  have hM_ge_rpow : (2 : ℝ) ^ absLogM N r (t + 1) ≤ (M : ℝ) := Nat.le_ceil _
  have habs_pos : 0 < absLogM N r (t + 1) := absLogM_pos hN hr (by omega)
  have hM_ge2 : 2 ≤ M := by
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ absLogM N r (t + 1) := by
      have : (1 : ℝ) ≤ absLogM N r (t + 1) := by
        unfold absLogM
        have h1' : (1 : ℝ) ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) :=
          one_le_pow₀ (by push_cast; linarith)
        have h2' : (1 : ℝ) ≤ (Real.logb 2 (r : ℝ)) ^ (t + 1) := one_le_pow₀ (by linarith)
        have h3' : (1 : ℝ) ≤ (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / ((t + 1 : ℕ) : ℝ)) :=
          Real.one_le_rpow (by linarith) (by positivity)
        calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
          _ ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) * (Real.logb 2 (r : ℝ)) ^ (t + 1) *
              (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / ((t + 1 : ℕ) : ℝ)) :=
            mul_le_mul (mul_le_mul h1' h2' (by positivity) (by positivity)) h3' (by positivity) (by positivity)
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ absLogM N r (t + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
    exact_mod_cast le_trans h1 hM_ge_rpow
  have habs_le_logN : absLogM N r (t + 1) ≤ Real.logb 2 (N : ℝ) := by
    rw [← Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (x := absLogM N r (t + 1))]
    exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
      (le_trans hM_ge_rpow (by exact_mod_cast hMN))
  have hlogM_ge : absLogM N r (t + 1) ≤ Real.logb 2 (M : ℝ) := by
    rw [← Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (x := absLogM N r (t + 1))]
    exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _) hM_ge_rpow
  have hlogM_le : Real.logb 2 (M : ℝ) ≤ absLogM N r (t + 1) + 1 := by
    have h1 : (M : ℝ) ≤ 2 * (2 : ℝ) ^ absLogM N r (t + 1) := by
      have hlt : (M : ℝ) < (2 : ℝ) ^ absLogM N r (t + 1) + 1 := Nat.ceil_lt_add_one (by positivity)
      have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ absLogM N r (t + 1) := Real.one_le_rpow (by norm_num) habs_pos.le
      linarith
    have h2 : 2 * (2 : ℝ) ^ absLogM N r (t + 1) = (2 : ℝ) ^ (absLogM N r (t + 1) + 1) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
    rw [h2] at h1
    calc Real.logb 2 (M : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ (absLogM N r (t + 1) + 1)) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
      _ = absLogM N r (t + 1) + 1 := Real.logb_rpow (by norm_num) (by norm_num)
  -- Step 1: define r' and bound log₂ r'
  set r' : ℕ := Nat.ceil ((2 : ℝ) ^ ((1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ)))
  have hr'_ge_rpow : (2 : ℝ) ^ ((1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ)) ≤ (r' : ℝ) := Nat.le_ceil _
  have hlogr'_ge : (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) ≤ Real.logb 2 (r' : ℝ) := by
    rw [← Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
      (x := (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ))]
    exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _) hr'_ge_rpow
  have hlogr'_le : Real.logb 2 (r' : ℝ) ≤ (1 + 4 / (t : ℝ)) * Real.logb 2 (r : ℝ) := by
    have h1 : (r' : ℝ) ≤ (2 : ℝ) ^ ((1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) + 1) := by
      have hlt : (r' : ℝ) < (2 : ℝ) ^ ((1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ)) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
      linarith
    have h2 : Real.logb 2 (r' : ℝ) ≤ (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) + 1 := by
      calc Real.logb 2 (r' : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ ((1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) + 1)) :=
            Real.logb_le_logb_of_le (by norm_num) (by
              have : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ)) :=
                Real.one_le_rpow (by norm_num) (by positivity)
              linarith) h1
        _ = (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) + 1 := Real.logb_rpow (by norm_num) (by norm_num)
    have h3 : (1 : ℝ) ≤ (1 / (t : ℝ)) * Real.logb 2 (r : ℝ) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ ht_pos]; linarith
    have h4 : (1 + 4 / (t : ℝ)) * Real.logb 2 (r : ℝ) =
        (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) + (1 / (t : ℝ)) * Real.logb 2 (r : ℝ) := by ring
    linarith
  have hlogr'_pos : 0 < Real.logb 2 (r' : ℝ) := by
    have : Real.logb 2 (r : ℝ) ≤ (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) := by
      have : (0 : ℝ) ≤ 3 / (t : ℝ) := by positivity
      nlinarith
    linarith
  have hr'_ge_r : r ≤ r' := by
    have h1 : (r : ℝ) ≤ (2 : ℝ) ^ ((1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ)) := by
      calc (r : ℝ) = (2 : ℝ) ^ Real.logb 2 (r : ℝ) :=
            (Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hr_pos).symm
        _ ≤ (2 : ℝ) ^ ((1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have : (0 : ℝ) ≤ 3 / (t : ℝ) := by positivity
            nlinarith
    exact_mod_cast le_trans h1 hr'_ge_rpow
  have hr'_ge2 : 2 ≤ r' := le_trans hr hr'_ge_r
  -- Step 2: define ℓ, log_n, n
  set ℓ : ℕ := Nat.floor (absLogM N r (t + 1) / (2 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)))
  have hratio_ge100 : (100 : ℝ) ≤ absLogM N r (t + 1) / (2 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : Real.logb 2 (r' : ℝ) ≤ 3 * Real.logb 2 (r : ℝ) := by
      have : 4 / (t : ℝ) ≤ 2 := by rw [div_le_iff₀ ht_pos]; linarith
      nlinarith
    have h2 : (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) ≥ 20000 * ((t : ℝ) + 1) := by
      have hbase : (1 : ℝ) ≤ 20000 * ((t + 1 : ℕ) : ℝ) := by push_cast; linarith
      calc 20000 * ((t : ℝ) + 1) = (20000 * ((t + 1 : ℕ) : ℝ)) ^ 1 := by push_cast; ring
        _ ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) := pow_le_pow_right₀ hbase (by omega)
    have h3 : (Real.logb 2 (r : ℝ)) ^ (t + 1) ≥ Real.logb 2 (r : ℝ) := by
      calc Real.logb 2 (r : ℝ) = (Real.logb 2 (r : ℝ)) ^ 1 := (pow_one _).symm
        _ ≤ (Real.logb 2 (r : ℝ)) ^ (t + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    have h4 : (1 : ℝ) ≤ (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / ((t + 1 : ℕ) : ℝ)) :=
      Real.one_le_rpow (by linarith) (by positivity)
    have h5 : (20000 * ((t : ℝ) + 1)) * Real.logb 2 (r : ℝ) ≤ absLogM N r (t + 1) := by
      unfold absLogM
      have h5a : (20000 * ((t : ℝ) + 1)) * Real.logb 2 (r : ℝ) ≤
          (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) * (Real.logb 2 (r : ℝ)) ^ (t + 1) :=
        mul_le_mul h2 h3 (by linarith) (by positivity)
      calc (20000 * ((t : ℝ) + 1)) * Real.logb 2 (r : ℝ)
          = (20000 * ((t : ℝ) + 1)) * Real.logb 2 (r : ℝ) * 1 := by ring
        _ ≤ ((20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) * (Real.logb 2 (r : ℝ)) ^ (t + 1)) *
            (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / ((t + 1 : ℕ) : ℝ)) :=
          mul_le_mul h5a h4 (by norm_num) (by positivity)
    nlinarith
  have hℓ_ge100 : 100 ≤ ℓ := Nat.le_floor hratio_ge100
  have hℓ_le : (ℓ : ℝ) ≤ absLogM N r (t + 1) / (2 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)) :=
    Nat.floor_le (by positivity)
  have hℓ_ge : absLogM N r (t + 1) / (4 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)) ≤ (ℓ : ℝ) := by
    have hlt := Nat.lt_floor_add_one (absLogM N r (t + 1) / (2 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)))
    have hhalf : absLogM N r (t + 1) / (4 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)) =
        (absLogM N r (t + 1) / (2 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ))) / 2 := by
      have hne : ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ) ≠ 0 := by positivity
      field_simp [hne]; ring
    linarith
  have hdiv_ge16 : (16 : ℝ) ≤ Real.logb 2 (N : ℝ) / (ℓ : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    have hden_ge : (32 : ℝ) ≤ 2 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ) := by
      have : (42 : ℝ) ≤ Real.logb 2 (r' : ℝ) := by
        have : Real.logb 2 (r : ℝ) ≤ (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) := by
          have : (0 : ℝ) ≤ 3 / (t : ℝ) := by positivity
          nlinarith
        linarith
      nlinarith
    have h1 : (ℓ : ℝ) ≤ Real.logb 2 (N : ℝ) / 32 := by
      calc (ℓ : ℝ) ≤ absLogM N r (t + 1) / (2 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)) := hℓ_le
        _ ≤ Real.logb 2 (N : ℝ) / (2 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)) :=
            div_le_div_of_nonneg_right habs_le_logN (by positivity)
        _ ≤ Real.logb 2 (N : ℝ) / 32 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hden_ge
    linarith
  set log_n : ℕ := Nat.ceil (Real.logb 2 (N : ℝ) / (ℓ : ℝ))
  have hlogn_ge16 : 16 ≤ log_n := by
    have : (16 : ℝ) ≤ (log_n : ℝ) := le_trans hdiv_ge16 (Nat.le_ceil _)
    exact_mod_cast this
  set n : ℕ := 2 ^ log_n
  have hn_ge16 : 16 ≤ n := by
    have : 2 ^ 4 ≤ 2 ^ log_n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlogn_eq : Real.logb 2 (n : ℝ) = (log_n : ℝ) := by
    simp only [n, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hlogn_le_logN : (log_n : ℝ) ≤ Real.logb 2 (N : ℝ) := by
    have h1 : (log_n : ℝ) < Real.logb 2 (N : ℝ) / (ℓ : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : Real.logb 2 (N : ℝ) / (ℓ : ℝ) ≤ Real.logb 2 (N : ℝ) / 100 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) (by exact_mod_cast hℓ_ge100)
    linarith
  have hlogn_ub : (log_n : ℝ) ≤ 8 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ) * Real.logb 2 (N : ℝ) /
      absLogM N r (t + 1) := by
    have h1 : (log_n : ℝ) ≤ 2 * (Real.logb 2 (N : ℝ) / (ℓ : ℝ)) := by
      have hlt : (log_n : ℝ) < Real.logb 2 (N : ℝ) / (ℓ : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    have h2 : Real.logb 2 (N : ℝ) / (ℓ : ℝ) ≤
        Real.logb 2 (N : ℝ) / (absLogM N r (t + 1) / (4 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ))) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hℓ_ge
    have h3 : 2 * (Real.logb 2 (N : ℝ) / (absLogM N r (t + 1) / (4 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)))) =
        8 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ) * Real.logb 2 (N : ℝ) / absLogM N r (t + 1) := by
      have hne1 : absLogM N r (t + 1) ≠ 0 := habs_pos.ne'
      have hne2 : 4 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ) ≠ 0 := by positivity
      field_simp [hne1, hne2]; ring
    linarith
  have hN_le_nl : N ≤ n ^ ℓ := by
    have h1 : Real.logb 2 (N : ℝ) ≤ (ℓ : ℝ) * (log_n : ℝ) := by
      rw [mul_comm]
      exact (div_le_iff₀ (by positivity)).mp (Nat.le_ceil _)
    have h2 : (N : ℝ) ≤ (2 : ℝ) ^ ((ℓ : ℝ) * (log_n : ℝ)) := by
      rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hN_pos]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    have h3 : (2 : ℝ) ^ ((ℓ : ℝ) * (log_n : ℝ)) = ((n ^ ℓ : ℕ) : ℝ) := by
      simp only [n, Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_mul, mul_comm, ← Real.rpow_natCast, Nat.cast_mul]
    rw [h3] at h2
    exact_mod_cast h2
  -- Step 3: apply IH to (n, r', t) and scramble
  have hih_cond : (t : ℝ) * (Real.logb 2 (Real.logb 2 (n : ℝ)) + 12) ≤ Real.logb 2 (r' : ℝ) := by
    have hloglog_le : Real.logb 2 (Real.logb 2 (n : ℝ)) ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) := by
      rw [hlogn_eq]
      exact Real.logb_le_logb_of_le (by norm_num) (by positivity) hlogn_le_logN
    have h1 : (t : ℝ) * (Real.logb 2 (Real.logb 2 (n : ℝ)) + 12) ≤
        ((t + 1 : ℕ) : ℝ) * (Real.logb 2 (Real.logb 2 (N : ℝ)) + 12) := by
      have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
      nlinarith only [hcast, hloglog_le, hloglogN_ge2, ht_ge2]
    have h2 : Real.logb 2 (r : ℝ) ≤ Real.logb 2 (r' : ℝ) := by
      have h3t : (0 : ℝ) ≤ 3 / (t : ℝ) := by positivity
      nlinarith only [h3t, hlogr'_ge, hlogr_ge42]
    linarith only [h1, h2, hcond]
  obtain ⟨G, hG⟩ := ih n r' hn_ge16 hr'_ge2 hih_cond
  have hlog256_le : Real.logb 2 (256 * Real.logb 2 (n : ℝ)) ≤ (1 / (t : ℝ)) * Real.logb 2 (r : ℝ) := by
    rw [Real.logb_mul (by norm_num) (by rw [hlogn_eq]; positivity)]
    have h256 : Real.logb 2 (256 : ℝ) = 8 := by
      rw [show (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      ring
    have hloglog_le : Real.logb 2 (Real.logb 2 (n : ℝ)) ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) := by
      rw [hlogn_eq]
      exact Real.logb_le_logb_of_le (by norm_num) (by positivity) hlogn_le_logN
    rw [h256, one_div, inv_mul_eq_div, le_div_iff₀ ht_pos]
    have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
    nlinarith only [hcast, hloglog_le, hloglogN_ge2, ht_ge2, hcond]
  have h256_le_r' : 256 * Real.logb 2 (n : ℝ) ≤ (r' : ℝ) := by
    have h256_pos : (0 : ℝ) < 256 * Real.logb 2 (n : ℝ) := by rw [hlogn_eq]; positivity
    have hr'_pos : (0 : ℝ) < (r' : ℝ) := by positivity
    calc 256 * Real.logb 2 (n : ℝ)
        = (2 : ℝ) ^ Real.logb 2 (256 * Real.logb 2 (n : ℝ)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) h256_pos).symm
      _ ≤ (2 : ℝ) ^ Real.logb 2 (r' : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have h1 : (1 / (t : ℝ)) * Real.logb 2 (r : ℝ) ≤ (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) := by
            have h2t : (0 : ℝ) ≤ 1 + 2 / (t : ℝ) := by positivity
            have hdiff : (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) - (1 / (t : ℝ)) * Real.logb 2 (r : ℝ) =
                (1 + 2 / (t : ℝ)) * Real.logb 2 (r : ℝ) := by ring
            nlinarith only [h2t, hdiff, hlogr_ge42]
          linarith only [h1, hlog256_le, hlogr'_ge]
      _ = (r' : ℝ) := Real.rpow_logb (by norm_num) (by norm_num) hr'_pos
  obtain ⟨G', hG'₂, hG'₃⟩ := scramble_locally_ramsey hn_ge16 h256_le_r' G hG
  set m₂ := r' / 2
  set m₃ := Nat.ceil ((2 : ℝ) ^ absLogM n r' t)
  set r₃ := Nat.ceil ((r' : ℝ) / (256 * Real.logb 2 (n : ℝ)))
  have hlogr₃_ge : (1 + 2 / (t : ℝ)) * Real.logb 2 (r : ℝ) ≤ Real.logb 2 (r₃ : ℝ) := by
    have hr₃_lb : (r' : ℝ) / (256 * Real.logb 2 (n : ℝ)) ≤ (r₃ : ℝ) := Nat.le_ceil _
    have h1 : Real.logb 2 ((r' : ℝ) / (256 * Real.logb 2 (n : ℝ))) ≤ Real.logb 2 (r₃ : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by rw [hlogn_eq]; positivity) hr₃_lb
    rw [Real.logb_div (by positivity) (by rw [hlogn_eq]; positivity)] at h1
    have h2 : (1 + 2 / (t : ℝ)) * Real.logb 2 (r : ℝ) =
        (1 + 3 / (t : ℝ)) * Real.logb 2 (r : ℝ) - (1 / (t : ℝ)) * Real.logb 2 (r : ℝ) := by ring
    linarith only [h1, h2, hlogr'_ge, hlog256_le]
  have hr₃_ge2 : 2 ≤ r₃ := by
    have hr₃_pos : (0 : ℝ) < (r₃ : ℝ) := by
      have : (0 : ℝ) < (r' : ℝ) / (256 * Real.logb 2 (n : ℝ)) := by rw [hlogn_eq]; positivity
      exact lt_of_lt_of_le this (Nat.le_ceil _)
    have h1 : (2 : ℝ) ≤ (r₃ : ℝ) := by
      have hge1 : (1 : ℝ) ≤ Real.logb 2 (r₃ : ℝ) := by
        have h2t : (0 : ℝ) ≤ 2 / (t : ℝ) := by positivity
        nlinarith only [h2t, hlogr₃_ge, hlogr_ge42]
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ Real.logb 2 (r₃ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hge1
        _ = (r₃ : ℝ) := Real.rpow_logb (by norm_num) (by norm_num) hr₃_pos
    exact_mod_cast h1
  have hm₂_ge2 : 2 ≤ m₂ := by
    have : (1024 : ℝ) ≤ (r' : ℝ) := by
      have : (4 : ℝ) ≤ Real.logb 2 (n : ℝ) := by rw [hlogn_eq]; exact_mod_cast (by omega : 4 ≤ log_n)
      linarith
    have : 1024 ≤ r' := by exact_mod_cast this
    omega
  have hm₃_ge1 : 1 ≤ m₃ := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ absLogM n r' t :=
      Real.one_le_rpow (by norm_num) (absLogM_pos hn_ge16 hr'_ge2 ht).le
    exact_mod_cast le_trans this (Nat.le_ceil _)
  -- Step 4: apply lexPow_caseB and embed Fin N ↪ (Fin ℓ → Fin n)
  have hcard_le : Fintype.card (Fin N) ≤ Fintype.card (Fin ℓ → Fin n) := by
    simpa [Fintype.card_fin] using hN_le_nl
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard_le
  refine ⟨(lexPow G' ℓ).comap ι, isLocallyRamsey_comap (lexPow G' ℓ) ι (fun S hScard => ?_)⟩
  have hS1 : 1 ≤ S.card := by omega
  have hSM : S.card ≤ M := by omega
  obtain ⟨⟨Cl, hClS, hClc, hCl⟩, ⟨Ind, hIndS, hIndc, hInd⟩⟩ :=
    lexPow_caseB hm₂_ge2 hm₃_ge1 hr₃_ge2 hM_ge2 G' hG'₂ hG'₃ ℓ S hS1 hSM
  set C : ℝ := max (Real.logb 2 (4 * (m₃ : ℝ))) (Real.logb 2 (M : ℝ) / Real.logb 2 (r₃ : ℝ))
  have hC_pos : 0 < C := by
    apply lt_of_lt_of_le _ (le_max_left _ _)
    apply Real.logb_pos (by norm_num)
    have : (1 : ℝ) ≤ (m₃ : ℝ) := by exact_mod_cast hm₃_ge1
    linarith
  have hr_le : (r : ℝ) ≤ (2 : ℝ) ^ ((Real.logb 2 (S.card : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ))) / C) := by
    rw [hScard]
    rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hr_pos]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [le_div_iff₀ hC_pos]
    -- Lower bound on numerator: log₂ M - ℓ * log₂ (2 m₂) ≥ (1 - 1 / (2*(t+2))) * absLogM
    have h2m₂_le : (2 * (m₂ : ℝ)) ≤ (r' : ℝ) := by
      have : 2 * m₂ ≤ r' := by omega
      exact_mod_cast this
    have hlog_2m₂ : Real.logb 2 (2 * (m₂ : ℝ)) ≤ Real.logb 2 (r' : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) h2m₂_le
    have hℓ_sub : (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ)) ≤ absLogM N r (t + 1) / (2 * ((t : ℝ) + 2)) := by
      have h1 : (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ)) ≤ (ℓ : ℝ) * Real.logb 2 (r' : ℝ) :=
        mul_le_mul_of_nonneg_left hlog_2m₂ (Nat.cast_nonneg ℓ)
      have h2 : (ℓ : ℝ) * Real.logb 2 (r' : ℝ) ≤ absLogM N r (t + 1) / (2 * ((t : ℝ) + 2)) := by
        have h3 := mul_le_mul_of_nonneg_right hℓ_le hlogr'_pos.le
        have h4 : absLogM N r (t + 1) / (2 * ((t : ℝ) + 2) * Real.logb 2 (r' : ℝ)) * Real.logb 2 (r' : ℝ) =
            absLogM N r (t + 1) / (2 * ((t : ℝ) + 2)) := by
          field_simp [hlogr'_pos.ne']
        linarith
      linarith
    have hnum_lb : (1 - 1 / (2 * ((t : ℝ) + 2))) * absLogM N r (t + 1) ≤
        Real.logb 2 (M : ℝ) - (ℓ : ℝ) * Real.logb 2 (2 * (m₂ : ℝ)) := by
      have : (1 - 1 / (2 * ((t : ℝ) + 2))) * absLogM N r (t + 1) =
          absLogM N r (t + 1) - absLogM N r (t + 1) / (2 * ((t : ℝ) + 2)) := by ring
      linarith
    -- It suffices to bound both branches of C * log₂ r ≤ (1 - 1/(2*(t+2))) * absLogM
    suffices hboth : Real.logb 2 (r : ℝ) * C ≤ (1 - 1 / (2 * ((t : ℝ) + 2))) * absLogM N r (t + 1) by
      linarith
    rw [mul_max_of_nonneg _ _ (by linarith : 0 ≤ Real.logb 2 (r : ℝ))]
    refine max_le ?_ ?_
    · -- Branch 1: log₂ r * log₂ (4 * m₃) ≤ (1 - 1/(2*(t+2))) * absLogM
      have hm₃_ub : Real.logb 2 (4 * (m₃ : ℝ)) ≤ 3 + absLogM n r' t := by
        have h1 : (4 * (m₃ : ℝ)) ≤ (2 : ℝ) ^ (absLogM n r' t + 3) := by
          have hlt : (m₃ : ℝ) < (2 : ℝ) ^ absLogM n r' t + 1 := Nat.ceil_lt_add_one (by positivity)
          have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ absLogM n r' t :=
            Real.one_le_rpow (by norm_num) (absLogM_pos hn_ge16 hr'_ge2 ht).le
          rw [Real.rpow_add (by norm_num)]
          norm_num; linarith
        calc Real.logb 2 (4 * (m₃ : ℝ)) ≤ Real.logb 2 ((2 : ℝ) ^ (absLogM n r' t + 3)) :=
              Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
          _ = absLogM n r' t + 3 := Real.logb_rpow (by norm_num) (by norm_num)
          _ = 3 + absLogM n r' t := by ring
      have h3_le : 3 * Real.logb 2 (r : ℝ) ≤ absLogM N r (t + 1) / 4 := by
        have h1 : (20000 * ((t : ℝ) + 1)) * Real.logb 2 (r : ℝ) ≤ absLogM N r (t + 1) := by
          unfold absLogM
          have h2 : 20000 * ((t : ℝ) + 1) ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) := by
            have hbase : (1 : ℝ) ≤ 20000 * ((t + 1 : ℕ) : ℝ) := by push_cast; linarith
            calc 20000 * ((t : ℝ) + 1) = (20000 * ((t + 1 : ℕ) : ℝ)) ^ 1 := by push_cast; ring
              _ ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) := pow_le_pow_right₀ hbase (by omega)
          have h3 : Real.logb 2 (r : ℝ) ≤ (Real.logb 2 (r : ℝ)) ^ (t + 1) := by
            calc Real.logb 2 (r : ℝ) = (Real.logb 2 (r : ℝ)) ^ 1 := (pow_one _).symm
              _ ≤ (Real.logb 2 (r : ℝ)) ^ (t + 1) := pow_le_pow_right₀ (by linarith) (by omega)
          have h4 : (1 : ℝ) ≤ (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / ((t + 1 : ℕ) : ℝ)) :=
            Real.one_le_rpow (by linarith) (by positivity)
          have h5 := mul_le_mul h2 h3 (by linarith) (by positivity)
          calc (20000 * ((t : ℝ) + 1)) * Real.logb 2 (r : ℝ)
              = (20000 * ((t : ℝ) + 1)) * Real.logb 2 (r : ℝ) * 1 := by ring
            _ ≤ ((20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) * (Real.logb 2 (r : ℝ)) ^ (t + 1)) *
                (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / ((t + 1 : ℕ) : ℝ)) :=
              mul_le_mul h5 h4 (by norm_num) (by positivity)
        nlinarith only [h1, ht_ge2, hlogr_ge42]
      have hcore : Real.logb 2 (r : ℝ) * absLogM n r' t ≤ absLogM N r (t + 1) / 4 :=
        absLogM_step_core ht hlogN_ge4 hlogr_ge42 hlogr'_pos hlogr'_le
          (by rw [hlogn_eq]; positivity) habs_pos (by rwa [hlogn_eq])
      have hhalf : (1 / 2 : ℝ) ≤ 1 - 1 / (2 * ((t : ℝ) + 2)) := by
        have : 1 / (2 * ((t : ℝ) + 2)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [ht_ge2]
        linarith only [this]
      have hsum : Real.logb 2 (r : ℝ) * Real.logb 2 (4 * (m₃ : ℝ)) ≤ absLogM N r (t + 1) / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hm₃_ub (by linarith only [hlogr_ge42] : 0 ≤ Real.logb 2 (r : ℝ))
        linarith only [hmul, h3_le, hcore]
      nlinarith only [hsum, hhalf, habs_pos]
    · -- Branch 2: log₂ r * (log₂ M / log₂ r₃) ≤ (1 - 1/(2*(t+2))) * absLogM
      have hlogr₃_pos : 0 < Real.logb 2 (r₃ : ℝ) := by
        have h2t : (0 : ℝ) ≤ 2 / (t : ℝ) := by positivity
        nlinarith only [h2t, hlogr₃_ge, hlogr_ge42]
      have hfrac_le : Real.logb 2 (r : ℝ) / Real.logb 2 (r₃ : ℝ) ≤ 1 - 2 / ((t : ℝ) + 2) := by
        rw [div_le_iff₀ hlogr₃_pos]
        have h1 : (1 - 2 / ((t : ℝ) + 2)) * ((1 + 2 / (t : ℝ)) * Real.logb 2 (r : ℝ)) =
            Real.logb 2 (r : ℝ) := by
          have ht2 : (t : ℝ) + 2 ≠ 0 := by linarith only [ht_ge2]
          field_simp [ht_pos.ne', ht2]; ring
        have h2 : (1 - 2 / ((t : ℝ) + 2)) * ((1 + 2 / (t : ℝ)) * Real.logb 2 (r : ℝ)) ≤
            (1 - 2 / ((t : ℝ) + 2)) * Real.logb 2 (r₃ : ℝ) :=
          mul_le_mul_of_nonneg_left hlogr₃_ge (by
            rw [sub_nonneg, div_le_one (by linarith only [ht_ge2])]; linarith only [ht_ge2])
        linarith only [h1, h2]
      have hrew : Real.logb 2 (r : ℝ) * (Real.logb 2 (M : ℝ) / Real.logb 2 (r₃ : ℝ)) =
          Real.logb 2 (M : ℝ) * (Real.logb 2 (r : ℝ) / Real.logb 2 (r₃ : ℝ)) := by ring
      rw [hrew]
      have h1 : Real.logb 2 (M : ℝ) * (Real.logb 2 (r : ℝ) / Real.logb 2 (r₃ : ℝ)) ≤
          (absLogM N r (t + 1) + 1) * (1 - 2 / ((t : ℝ) + 2)) :=
        mul_le_mul hlogM_le hfrac_le (by positivity) (by linarith only [habs_pos])
      have habs_big : 2 * ((t : ℝ) + 2) ≤ absLogM N r (t + 1) := by
        unfold absLogM
        have h2 : 20000 * ((t : ℝ) + 1) ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) := by
          have hbase : (1 : ℝ) ≤ 20000 * ((t + 1 : ℕ) : ℝ) := by push_cast; linarith only [ht_ge2]
          calc 20000 * ((t : ℝ) + 1) = (20000 * ((t + 1 : ℕ) : ℝ)) ^ 1 := by push_cast; ring
            _ ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) := pow_le_pow_right₀ hbase (by omega)
        have h3 : (1 : ℝ) ≤ (Real.logb 2 (r : ℝ)) ^ (t + 1) := one_le_pow₀ (by linarith only [hlogr_ge42])
        have h4 : (1 : ℝ) ≤ (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / ((t + 1 : ℕ) : ℝ)) :=
          Real.one_le_rpow (by linarith only [hlogN_ge4]) (by positivity)
        have h23 : 20000 * ((t : ℝ) + 1) ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) * (Real.logb 2 (r : ℝ)) ^ (t + 1) := by
          calc 20000 * ((t : ℝ) + 1) = 20000 * ((t : ℝ) + 1) * 1 := by ring
            _ ≤ _ := mul_le_mul h2 h3 (by norm_num) (by positivity)
        have h234 : 20000 * ((t : ℝ) + 1) ≤ (20000 * ((t + 1 : ℕ) : ℝ)) ^ (t + 1) * (Real.logb 2 (r : ℝ)) ^ (t + 1) *
            (Real.logb 2 (N : ℝ)) ^ ((1 : ℝ) / ((t + 1 : ℕ) : ℝ)) := by
          calc 20000 * ((t : ℝ) + 1) = 20000 * ((t : ℝ) + 1) * 1 := by ring
            _ ≤ _ := mul_le_mul h23 h4 (by norm_num) (by positivity)
        linarith only [h234, ht_ge2]
      have h2 : (absLogM N r (t + 1) + 1) * (1 - 2 / ((t : ℝ) + 2)) ≤
          (1 - 1 / (2 * ((t : ℝ) + 2))) * absLogM N r (t + 1) := by
        have h1_le : (1 : ℝ) ≤ absLogM N r (t + 1) / (2 * ((t : ℝ) + 2)) := by
          rw [one_le_div (by positivity)]; linarith only [habs_big]
        have hsub : (1 - 1 / (2 * ((t : ℝ) + 2))) * absLogM N r (t + 1) -
            (absLogM N r (t + 1) + 1) * (1 - 2 / ((t : ℝ) + 2)) =
            (3 * (absLogM N r (t + 1) / (2 * ((t : ℝ) + 2))) - 1) + 2 / ((t : ℝ) + 2) := by
          have ht2 : (t : ℝ) + 2 ≠ 0 := by linarith only [ht_ge2]
          field_simp [ht2]; ring
        have hpos2 : (0 : ℝ) ≤ 2 / ((t : ℝ) + 2) := by positivity
        linarith only [h1_le, hsub, hpos2]
      linarith only [h1, h2]
  exact ⟨⟨Cl, hClS, by exact_mod_cast le_trans hr_le hClc, hCl⟩,
    ⟨Ind, hIndS, by exact_mod_cast le_trans hr_le hIndc, hInd⟩⟩

private lemma locally_ramsey_iter (t : ℕ) (ht : 2 ≤ t) :
    ∀ N r : ℕ, 16 ≤ N → 2 ≤ r →
      (t : ℝ) * (Real.logb 2 (Real.logb 2 (N : ℝ)) + 12) ≤ Real.logb 2 (r : ℝ) →
      ∃ G : SimpleGraph (Fin N), IsLocallyRamsey G (Nat.ceil ((2 : ℝ) ^ absLogM N r t)) r := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht2 : t < 2
    · have ht1 : t = 1 := by omega
      subst ht1
      intro N r hN hr hcond
      exact locally_ramsey_base hN hr (by simpa using hcond)
    · exact locally_ramsey_step (by omega) (ih (by omega))

end Erdos805ABS

theorem OMA.solution : type_of% @Erdos805.erdos_805.variants.alon_bucic_sudakov := by
  intro ε hε_pos hε_lt
  open Filter Real Erdos805 Erdos805ABS in
  -- Show log₂(log₂ N) → ∞ as N → ∞
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htend_logN : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun x : ℝ => x / Real.log 2) atTop atTop :=
      Filter.Tendsto.atTop_div_const hlog2_pos tendsto_id
    exact h2.comp h1
  have htend_A : Tendsto (fun N : ℕ => Real.logb 2 (Real.logb 2 (N : ℝ))) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / Real.log 2) atTop atTop :=
      (Filter.Tendsto.atTop_div_const hlog2_pos tendsto_id).comp Real.tendsto_log_atTop
    exact h1.comp htend_logN
  -- For sufficiently large A, log₂ 40000 + 3 * log₂ A + 2 ≤ A ^ ε
  have hsmall_A : ∀ᶠ A : ℝ in atTop,
      Real.logb 2 40000 + 3 * Real.logb 2 A + 2 ≤ A ^ ε ∧ (16 : ℝ) ≤ A := by
    have h1 : (fun A : ℝ => Real.log A) =o[atTop] (fun A : ℝ => A ^ ε) :=
      isLittleO_log_rpow_atTop hε_pos
    have h2 : ∀ᶠ A : ℝ in atTop, ‖Real.log A‖ ≤ (Real.log 2 / 6) * ‖A ^ ε‖ :=
      h1.bound (by positivity)
    have h3 : ∀ᶠ A : ℝ in atTop, (2 * (Real.logb 2 40000 + 2)) ≤ A ^ ε :=
      (tendsto_rpow_atTop hε_pos).eventually (eventually_ge_atTop _)
    have h4 : ∀ᶠ A : ℝ in atTop, (16 : ℝ) ≤ A := eventually_ge_atTop 16
    filter_upwards [h2, h3, h4] with A hA2 hA3 hA4
    refine ⟨?_, hA4⟩
    have hA_pos : 0 < A := by linarith
    have hlogA_nn : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
    have hrpow_nn : 0 ≤ A ^ ε := (Real.rpow_pos_of_pos hA_pos ε).le
    rw [Real.norm_of_nonneg hlogA_nn, Real.norm_of_nonneg hrpow_nn] at hA2
    have hlogb_le : 3 * Real.logb 2 A ≤ A ^ ε / 2 := by
      rw [Real.logb]
      have : 3 * (Real.log A / Real.log 2) ≤ A ^ ε / 2 := by
        rw [show 3 * (Real.log A / Real.log 2) = (3 * Real.log A) / Real.log 2 by ring,
          div_le_iff₀ hlog2_pos]
        linarith
      exact this
    linarith
  have hev_N : ∀ᶠ N : ℕ in atTop,
      (Real.logb 2 40000 + 3 * Real.logb 2 (Real.logb 2 (Real.logb 2 (N : ℝ))) + 2 ≤
          (Real.logb 2 (Real.logb 2 (N : ℝ))) ^ ε ∧
        (16 : ℝ) ≤ Real.logb 2 (Real.logb 2 (N : ℝ))) ∧ 16 ≤ N :=
    (htend_A.eventually hsmall_A).and (eventually_ge_atTop 16)
  filter_upwards [hev_N] with N ⟨⟨hA_eps, hA_ge16⟩, hN_ge16⟩
  set A : ℝ := Real.logb 2 (Real.logb 2 (N : ℝ))
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.logb 2 (N : ℝ) := by
    apply Real.logb_pos (by norm_num); exact_mod_cast (by omega : 1 < N)
  have hA_pos : 0 < A := by linarith
  set t : ℕ := Nat.floor (Real.sqrt A)
  have hsqrt_ge4 : (4 : ℝ) ≤ Real.sqrt A := by
    rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
    exact Real.sqrt_le_sqrt hA_ge16
  have ht_ge4 : 4 ≤ t := Nat.le_floor hsqrt_ge4
  have ht_ge2 : 2 ≤ t := by omega
  have ht_le : (t : ℝ) ≤ Real.sqrt A := Nat.floor_le (Real.sqrt_nonneg A)
  have ht_ge : Real.sqrt A / 2 ≤ (t : ℝ) := by
    have := Nat.lt_floor_add_one (Real.sqrt A)
    linarith
  set r : ℕ := Nat.ceil ((2 : ℝ) ^ ((t : ℝ) * (A + 12)))
  have hr_ge_rpow : (2 : ℝ) ^ ((t : ℝ) * (A + 12)) ≤ (r : ℝ) := Nat.le_ceil _
  have hlogr_ge : (t : ℝ) * (A + 12) ≤ Real.logb 2 (r : ℝ) := by
    rw [← Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (x := (t : ℝ) * (A + 12))]
    exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _) hr_ge_rpow
  have hr_ge2 : 2 ≤ r := by
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ ((t : ℝ) * (A + 12)) := by
      have : (1 : ℝ) ≤ (t : ℝ) * (A + 12) := by
        have : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge4
        nlinarith
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ ((t : ℝ) * (A + 12)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
    exact_mod_cast le_trans h1 hr_ge_rpow
  have hceil_logN_le_r : Nat.ceil (Real.logb 2 (N : ℝ)) ≤ r := by
    apply Nat.ceil_le.mpr
    have h1 : Real.logb 2 (N : ℝ) = (2 : ℝ) ^ A :=
      (Real.rpow_logb (by norm_num) (by norm_num) hlogN_pos).symm
    rw [h1]
    have h2 : A ≤ (t : ℝ) * (A + 12) := by
      have : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge4
      nlinarith
    exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) h2) hr_ge_rpow
  obtain ⟨G, hG⟩ := locally_ramsey_iter t ht_ge2 N r hN_ge16 hr_ge2 hlogr_ge
  refine ⟨G, isLocallyRamsey_mono hG ?_ hceil_logN_le_r⟩
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  -- Show absLogM N r t ≤ 2 ^ (A ^ (1/2 + ε))
  have habs_pos : 0 < absLogM N r t := absLogM_pos hN_ge16 hr_ge2 ht_ge2
  rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) habs_pos]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  -- Bound log₂ (absLogM N r t) ≤ A ^ (1/2 + ε)
  have hlogr_le : Real.logb 2 (r : ℝ) ≤ 2 * A ^ 2 := by
    have h1 : (r : ℝ) ≤ (2 : ℝ) ^ ((t : ℝ) * (A + 12) + 1) := by
      have hlt : (r : ℝ) < (2 : ℝ) ^ ((t : ℝ) * (A + 12)) + 1 := Nat.ceil_lt_add_one (by positivity)
      have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((t : ℝ) * (A + 12)) := Real.one_le_rpow (by norm_num) (by positivity)
      rw [Real.rpow_add (by norm_num), Real.rpow_one]; linarith
    have h2 : Real.logb 2 (r : ℝ) ≤ (t : ℝ) * (A + 12) + 1 := by
      calc Real.logb 2 (r : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ ((t : ℝ) * (A + 12) + 1)) :=
            Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
        _ = (t : ℝ) * (A + 12) + 1 := Real.logb_rpow (by norm_num) (by norm_num)
    have hsqrt_le : Real.sqrt A ≤ A := by
      have := Real.sqrt_le_sqrt (by nlinarith : A ≤ A * A)
      rwa [Real.sqrt_mul_self hA_pos.le] at this
    nlinarith
  have hlog_abs : Real.logb 2 (absLogM N r t) =
      (t : ℝ) * Real.logb 2 (20000 * (t : ℝ)) + (t : ℝ) * Real.logb 2 (Real.logb 2 (r : ℝ)) +
        A / (t : ℝ) := by
    unfold absLogM
    have hlogr_pos : 0 < Real.logb 2 (r : ℝ) := by
      have : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge4
      nlinarith
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow, Real.logb_pow,
      Real.logb_rpow_eq_mul_logb_of_pos hlogN_pos]
    ring
  rw [hlog_abs]
  have h20000t : Real.logb 2 (20000 * (t : ℝ)) ≤ Real.logb 2 40000 + Real.logb 2 A := by
    have hsqrt_le : Real.sqrt A ≤ A := by
      have := Real.sqrt_le_sqrt (by nlinarith : A ≤ A * A)
      rwa [Real.sqrt_mul_self hA_pos.le] at this
    calc Real.logb 2 (20000 * (t : ℝ)) ≤ Real.logb 2 (40000 * A) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) (by nlinarith)
      _ = Real.logb 2 40000 + Real.logb 2 A := Real.logb_mul (by norm_num) hA_pos.ne'
  have hloglogr : Real.logb 2 (Real.logb 2 (r : ℝ)) ≤ 1 + 2 * Real.logb 2 A := by
    have hlogr_pos : 0 < Real.logb 2 (r : ℝ) := by
      have : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge4
      nlinarith
    calc Real.logb 2 (Real.logb 2 (r : ℝ)) ≤ Real.logb 2 (2 * A ^ 2) :=
          Real.logb_le_logb_of_le (by norm_num) hlogr_pos hlogr_le
      _ = Real.logb 2 2 + Real.logb 2 (A ^ 2) := Real.logb_mul (by norm_num) (by positivity)
      _ = 1 + 2 * Real.logb 2 A := by rw [Real.logb_self_eq_one (by norm_num), Real.logb_pow]; ring
  have hAt : A / (t : ℝ) ≤ 2 * Real.sqrt A := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA_pos.le
    nlinarith
  have hsqrt_eq : Real.sqrt A = A ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow A
  have hsqrt_rpow : Real.sqrt A * A ^ ε = A ^ (1 / 2 + ε) := by
    rw [hsqrt_eq, ← Real.rpow_add hA_pos]
  have h20000t' : Real.logb 2 (20000 * (t : ℝ)) ≤ Real.logb 2 40000 - 1 + Real.logb 2 A := by
    have hsqrt_le : Real.sqrt A ≤ A := by
      have := Real.sqrt_le_sqrt (by nlinarith : A ≤ A * A)
      rwa [Real.sqrt_mul_self hA_pos.le] at this
    have h40k : Real.logb 2 40000 = 1 + Real.logb 2 20000 := by
      rw [show (40000 : ℝ) = 2 * 20000 by norm_num, Real.logb_mul (by norm_num) (by norm_num),
        Real.logb_self_eq_one (by norm_num)]
    rw [h40k]
    calc Real.logb 2 (20000 * (t : ℝ)) ≤ Real.logb 2 (20000 * A) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) (by nlinarith)
      _ = Real.logb 2 20000 + Real.logb 2 A := Real.logb_mul (by norm_num) hA_pos.ne'
      _ = 1 + Real.logb 2 20000 - 1 + Real.logb 2 A := by ring
  have hcomb2 : (t : ℝ) * Real.logb 2 (20000 * (t : ℝ)) + (t : ℝ) * Real.logb 2 (Real.logb 2 (r : ℝ)) +
      A / (t : ℝ) ≤ Real.sqrt A * (Real.logb 2 40000 + 3 * Real.logb 2 A + 2) := by
    have hsum_le : Real.logb 2 (20000 * (t : ℝ)) + Real.logb 2 (Real.logb 2 (r : ℝ)) ≤
        Real.logb 2 40000 + 3 * Real.logb 2 A := by linarith
    have ht4 : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge4
    have hnn1 : 0 ≤ Real.logb 2 (20000 * (t : ℝ)) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    have hnn2 : 0 ≤ Real.logb 2 (Real.logb 2 (r : ℝ)) :=
      Real.logb_nonneg (by norm_num) (by nlinarith)
    have h1 := mul_le_mul ht_le hsum_le (by linarith) (Real.sqrt_nonneg A)
    linarith
  calc (t : ℝ) * Real.logb 2 (20000 * (t : ℝ)) + (t : ℝ) * Real.logb 2 (Real.logb 2 (r : ℝ)) + A / (t : ℝ)
      ≤ Real.sqrt A * (Real.logb 2 40000 + 3 * Real.logb 2 A + 2) := hcomb2
    _ ≤ Real.sqrt A * A ^ ε := mul_le_mul_of_nonneg_left hA_eps (Real.sqrt_nonneg A)
    _ = A ^ (1 / 2 + ε) := hsqrt_rpow
