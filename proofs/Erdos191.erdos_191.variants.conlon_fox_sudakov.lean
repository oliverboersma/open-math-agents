import FormalConjectures.ErdosProblems.«191»
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Calculus.MeanValue

-- Problem: Erdős Problem 191 — conlon fox sudakov
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/191.lean:81 (declaration Erdos191.erdos_191.variants.conlon_fox_sudakov)
-- Credit: @kDylanHayes

namespace Erdos191CFS

open Finset Filter Real SimpleGraph

/-! ### Part 1: Dependent Random Choice (Conlon-Fox-Sudakov Lemma 2.1) -/

private lemma card_piFinset_const {α : Type*} [DecidableEq α] (t : ℕ) (S : Finset α) :
    (Fintype.piFinset (fun _ : Fin t => S)).card = S.card ^ t := by
  simp [Fintype.card_piFinset]

private lemma sum_pow_ge_div_card {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) (hs : s.Nonempty) (t : ℕ) :
    (∑ x ∈ s, f x) ^ t ≤ (s.card : ℝ) ^ (t - 1) * ∑ x ∈ s, f x ^ t := by
  cases t with
  | zero =>
    simp only [pow_zero, Nat.zero_sub, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast hs.card_pos
  | succ k =>
    have hcard : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
    have hconv := convexOn_pow (𝕜 := ℝ) (k + 1)
    have hmem : ∀ x ∈ s, f x ∈ Set.Ici (0 : ℝ) := fun x hx => hf x hx
    have hw : ∀ x ∈ s, (0 : ℝ) ≤ (1 : ℝ) / s.card := fun _ _ => by positivity
    have hwsum : ∑ _x ∈ s, (1 : ℝ) / s.card = 1 := by
      simp [Finset.sum_const, nsmul_eq_mul, hcard.ne']
    have hj := hconv.map_sum_le hw hwsum hmem
    simp only [smul_eq_mul] at hj
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hj
    rw [mul_pow, one_div_pow, one_div_mul_eq_div, div_le_iff₀ (pow_pos hcard (k + 1))] at hj
    have hpow : (s.card : ℝ) ^ (k + 1) * (1 / (s.card : ℝ)) = (s.card : ℝ) ^ k := by
      rw [pow_succ, mul_assoc, mul_one_div_cancel hcard.ne', mul_one]
    calc (∑ x ∈ s, f x) ^ (k + 1)
        ≤ (1 / (s.card : ℝ) * ∑ x ∈ s, f x ^ (k + 1)) * (s.card : ℝ) ^ (k + 1) := hj
      _ = (s.card : ℝ) ^ (k + 1) * (1 / (s.card : ℝ)) * ∑ x ∈ s, f x ^ (k + 1) := by ring
      _ = (s.card : ℝ) ^ k * ∑ x ∈ s, f x ^ (k + 1) := by rw [hpow]

private lemma dependent_random_choice {α : Type*} [DecidableEq α]
    (V₁ V₂ : Finset α) (hV₁ : V₁.Nonempty) (hV₂ : V₂.Nonempty)
    (E : α → α → Prop) [DecidableRel E]
    (p : ℝ) (hp : 0 ≤ p) (s t m : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hedges : p * (V₁.card : ℝ) * (V₂.card : ℝ) ≤
      ∑ u ∈ V₁, ((V₂.filter (fun v => E u v)).card : ℝ))
    (hcond : (V₁.card.choose s : ℝ) * ((m : ℝ) / (V₂.card : ℝ)) ^ t ≤
      p ^ t * (V₁.card : ℝ) / 2) :
    ∃ U ⊆ V₁, p ^ t * (V₁.card : ℝ) / 2 ≤ (U.card : ℝ) ∧
      ∀ S ⊆ U, S.card = s → m ≤ (V₂.filter (fun v => ∀ u ∈ S, E u v)).card := by
  classical
  let TSet : Finset (Fin t → α) := Fintype.piFinset (fun _ : Fin t => V₂)
  have hTSet_card : TSet.card = V₂.card ^ t := card_piFinset_const t V₂
  have hTSet_pos : (0 : ℝ) < (TSet.card : ℝ) := by
    rw [hTSet_card]
    exact_mod_cast pow_pos hV₂.card_pos t
  let W : (Fin t → α) → Finset α := fun T => V₁.filter (fun u => ∀ i : Fin t, E u (T i))
  let Bad : Finset (Finset α) :=
    (V₁.powersetCard s).filter (fun S => (V₂.filter (fun v => ∀ u ∈ S, E u v)).card < m)
  let Y : (Fin t → α) → ℕ := fun T => (Bad.filter (fun S => S ⊆ W T)).card
  -- Step 1: Sum of |W T| over T in TSet
  have hsumW : ∑ T ∈ TSet, ((W T).card : ℝ) =
      ∑ u ∈ V₁, ((V₂.filter (fun v => E u v)).card : ℝ) ^ t := by
    norm_cast
    calc ∑ T ∈ TSet, (W T).card
        = ∑ T ∈ TSet, ∑ u ∈ V₁, if ∀ i : Fin t, E u (T i) then 1 else 0 := by
            refine Finset.sum_congr rfl fun T _ => ?_
            simp only [W, Finset.card_filter]
      _ = ∑ u ∈ V₁, ∑ T ∈ TSet, if ∀ i : Fin t, E u (T i) then 1 else 0 :=
            Finset.sum_comm
      _ = ∑ u ∈ V₁, (V₂.filter (fun v => E u v)).card ^ t := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [← Finset.card_filter]
            have heq : TSet.filter (fun T => ∀ i : Fin t, E u (T i)) =
                Fintype.piFinset (fun _ : Fin t => V₂.filter (fun v => E u v)) := by
              ext T
              simp [TSet, Fintype.mem_piFinset, Finset.mem_filter, forall_and]
            rw [heq, card_piFinset_const]
  -- Step 2: Lower bound on sum of |W T| by Jensen
  have hV₁_pos : (0 : ℝ) < V₁.card := Nat.cast_pos.mpr hV₁.card_pos
  have hV₂_pos : (0 : ℝ) < V₂.card := Nat.cast_pos.mpr hV₂.card_pos
  have hsumW_lb : p ^ t * (V₁.card : ℝ) * (V₂.card : ℝ) ^ t ≤
      ∑ T ∈ TSet, ((W T).card : ℝ) := by
    rw [hsumW]
    have hj := sum_pow_ge_div_card V₁ (fun u => ((V₂.filter (fun v => E u v)).card : ℝ))
      (fun u _ => Nat.cast_nonneg _) hV₁ t
    have hpow : (p * (V₁.card : ℝ) * (V₂.card : ℝ)) ^ t ≤
        (∑ u ∈ V₁, ((V₂.filter (fun v => E u v)).card : ℝ)) ^ t :=
      pow_le_pow_left₀ (by positivity) hedges t
    have hcomb := le_trans hpow hj
    have hrewrite : (p * (V₁.card : ℝ) * (V₂.card : ℝ)) ^ t =
        (V₁.card : ℝ) ^ (t - 1) * (p ^ t * (V₁.card : ℝ) * (V₂.card : ℝ) ^ t) := by
      rw [mul_pow, mul_pow]
      have : (V₁.card : ℝ) ^ (t - 1) * (V₁.card : ℝ) = (V₁.card : ℝ) ^ t := by
        rw [← pow_succ, Nat.sub_add_cancel ht]
      calc p ^ t * (V₁.card : ℝ) ^ t * (V₂.card : ℝ) ^ t
          = p ^ t * ((V₁.card : ℝ) ^ (t - 1) * (V₁.card : ℝ)) * (V₂.card : ℝ) ^ t := by
              rw [this]
        _ = (V₁.card : ℝ) ^ (t - 1) * (p ^ t * (V₁.card : ℝ) * (V₂.card : ℝ) ^ t) := by ring
    rw [hrewrite] at hcomb
    exact le_of_mul_le_mul_left hcomb (pow_pos hV₁_pos (t - 1))
  -- Step 3: Upper bound on sum of Y T
  have hsumY_ub : ∑ T ∈ TSet, (Y T : ℝ) ≤ (V₁.card.choose s : ℝ) * (m : ℝ) ^ t := by
    have hsumY : ∑ T ∈ TSet, Y T =
        ∑ S ∈ Bad, (V₂.filter (fun v => ∀ u ∈ S, E u v)).card ^ t := by
      calc ∑ T ∈ TSet, Y T
          = ∑ T ∈ TSet, ∑ S ∈ Bad, if S ⊆ W T then 1 else 0 := by
              refine Finset.sum_congr rfl fun T _ => ?_
              simp only [Y, Finset.card_filter]
        _ = ∑ S ∈ Bad, ∑ T ∈ TSet, if S ⊆ W T then 1 else 0 := Finset.sum_comm
        _ = ∑ S ∈ Bad, (V₂.filter (fun v => ∀ u ∈ S, E u v)).card ^ t := by
              refine Finset.sum_congr rfl fun S hS => ?_
              rw [← Finset.card_filter]
              have hSV₁ : S ⊆ V₁ := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1
              have heq : TSet.filter (fun T => S ⊆ W T) =
                  Fintype.piFinset (fun _ : Fin t => V₂.filter (fun v => ∀ u ∈ S, E u v)) := by
                ext T
                simp only [TSet, W, Finset.mem_filter, Fintype.mem_piFinset, Finset.subset_iff]
                constructor
                · rintro ⟨hT, hsub⟩ i
                  exact ⟨hT i, fun u hu => (hsub hu).2 i⟩
                · intro h
                  refine ⟨fun i => (h i).1, fun u hu => ⟨hSV₁ hu, fun i => (h i).2 u hu⟩⟩
              rw [heq, card_piFinset_const]
    have hnat : ∑ T ∈ TSet, Y T ≤ V₁.card.choose s * m ^ t := by
      rw [hsumY]
      calc ∑ S ∈ Bad, (V₂.filter (fun v => ∀ u ∈ S, E u v)).card ^ t
          ≤ ∑ _S ∈ Bad, m ^ t := by
              refine Finset.sum_le_sum fun S hS => ?_
              exact Nat.pow_le_pow_left (le_of_lt (Finset.mem_filter.mp hS).2) t
        _ = Bad.card * m ^ t := by simp
        _ ≤ V₁.card.choose s * m ^ t := by
              apply Nat.mul_le_mul_right
              have := Finset.card_le_card (Finset.filter_subset
                (fun S => (V₂.filter (fun v => ∀ u ∈ S, E u v)).card < m) (V₁.powersetCard s))
              simpa [Finset.card_powersetCard] using this
    exact_mod_cast hnat
  -- Step 4: Difference sum and averaging
  have hcond' : (V₁.card.choose s : ℝ) * (m : ℝ) ^ t ≤
      p ^ t * (V₁.card : ℝ) / 2 * (V₂.card : ℝ) ^ t := by
    have h1 := mul_le_mul_of_nonneg_right hcond (pow_nonneg hV₂_pos.le t)
    rwa [mul_assoc, div_pow, div_mul_cancel₀ _ (pow_ne_zero t hV₂_pos.ne')] at h1
  have hdiff_sum : (p ^ t * (V₁.card : ℝ) / 2) * (TSet.card : ℝ) ≤
      ∑ T ∈ TSet, (((W T).card : ℝ) - (Y T : ℝ)) := by
    rw [Finset.sum_sub_distrib, hTSet_card, Nat.cast_pow]
    linarith
  have hexT : ∃ T ∈ TSet, p ^ t * (V₁.card : ℝ) / 2 ≤ ((W T).card : ℝ) - (Y T : ℝ) := by
    by_contra hnot
    push Not at hnot
    have hlt : ∑ T ∈ TSet, (((W T).card : ℝ) - (Y T : ℝ)) <
        ∑ _T ∈ TSet, (p ^ t * (V₁.card : ℝ) / 2) :=
      Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by rw [hTSet_card]; exact pow_pos hV₂.card_pos t)) hnot
    simp only [Finset.sum_const, nsmul_eq_mul] at hlt
    linarith
  obtain ⟨T, -, hT⟩ := hexT
  -- Step 5: Delete one vertex from each bad s-subset of W T
  let BadW := Bad.filter (fun S => S ⊆ W T)
  have hBadW_ne : ∀ S ∈ BadW, S.Nonempty := by
    intro S hS
    have hcardS : S.card = s :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2
    exact Finset.card_pos.mp (by omega)
  let pick : Finset α → α := fun S =>
    if h : S.Nonempty then h.choose else hV₁.choose
  have hpick_mem : ∀ S ∈ BadW, pick S ∈ S := by
    intro S hS
    have hne := hBadW_ne S hS
    simp only [pick, dif_pos hne]
    exact hne.choose_spec
  let Del := BadW.image pick
  let U := W T \ Del
  refine ⟨U, (Finset.sdiff_subset).trans (Finset.filter_subset _ V₁), ?_, ?_⟩
  · have hDel_le : Del.card ≤ Y T := Finset.card_image_le
    have hU_card : (W T).card - Y T ≤ U.card := by
      have h1 : (W T).card - Del.card ≤ U.card := Finset.le_card_sdiff Del (W T)
      omega
    have hcast : ((W T).card : ℝ) - (Y T : ℝ) ≤ (U.card : ℝ) := by
      by_cases hle : Y T ≤ (W T).card
      · have := Nat.cast_le (α := ℝ).mpr hU_card
        rwa [Nat.cast_sub hle] at this
      · have : ((W T).card : ℝ) - (Y T : ℝ) ≤ 0 := by
          have : (W T).card < Y T := Nat.lt_of_not_le hle
          have : ((W T).card : ℝ) < (Y T : ℝ) := Nat.cast_lt.mpr this
          linarith
        exact this.trans (Nat.cast_nonneg _)
    linarith
  · intro S hSU hScard
    by_contra hlt
    push Not at hlt
    have hSW : S ⊆ W T := hSU.trans Finset.sdiff_subset
    have hSV₁ : S ⊆ V₁ := hSW.trans (Finset.filter_subset _ V₁)
    have hSBadW : S ∈ BadW :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hSV₁, hScard⟩, hlt⟩, hSW⟩
    have hpU : pick S ∈ U := hSU (hpick_mem S hSBadW)
    have hpDel : pick S ∈ Del := Finset.mem_image_of_mem pick hSBadW
    exact (Finset.mem_sdiff.mp hpU).2 hpDel

/- ### Part 2: Erdos-Szekeres and Asymmetric Ramsey Bounds (Lemma 3.1) -/

private lemma ramsey_erdos_szekeres {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ n s t : ℕ, 1 ≤ s → 1 ≤ t → s + t = n →
      ∀ U : Finset V, (s + t - 2).choose (s - 1) ≤ U.card →
        (∃ K ⊆ U, G.IsClique (K : Set V) ∧ K.card = s) ∨
        (∃ L ⊆ U, G.IsIndepSet (L : Set V) ∧ L.card = t) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s t hs ht hst U hU
    by_cases hs1 : s = 1
    · subst hs1
      have hne : U.Nonempty := Finset.card_pos.mp (by
        rw [Nat.sub_self, Nat.choose_zero_right] at hU
        omega)
      obtain ⟨v, hv⟩ := hne
      exact Or.inl ⟨{v}, Finset.singleton_subset_iff.mpr hv, by simp, by simp⟩
    by_cases ht1 : t = 1
    · subst ht1
      have hne : U.Nonempty := Finset.card_pos.mp (by
        have hpos : (s + 1 - 2).choose (s - 1) = 1 := by
          have : s + 1 - 2 = s - 1 := by omega
          rw [this, Nat.choose_self]
        omega)
      obtain ⟨v, hv⟩ := hne
      exact Or.inr ⟨{v}, Finset.singleton_subset_iff.mpr hv, by simp, by simp⟩
    have hs2 : 2 ≤ s := by omega
    have ht2 : 2 ≤ t := by omega
    have hchoose_eq : (s + t - 2).choose (s - 1) =
        (s - 1 + t - 2).choose (s - 2) + (s + (t - 1) - 2).choose (s - 1) := by
      have h1 : s + t - 2 = (s + t - 3) + 1 := by omega
      have h2 : s - 1 = (s - 2) + 1 := by omega
      have h3 : s - 1 + t - 2 = s + t - 3 := by omega
      have h4 : s + (t - 1) - 2 = s + t - 3 := by omega
      rw [h3, h4, h1, h2, Nat.choose_succ_succ]
    have hUpos : 0 < U.card := by
      have : 0 < (s + t - 2).choose (s - 1) := Nat.choose_pos (by omega)
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hUpos
    let R := (U.erase v).filter (fun w => G.Adj v w)
    let B := (U.erase v).filter (fun w => ¬ G.Adj v w)
    have hRB : R.card + B.card = U.card - 1 := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
    by_cases hR : (s - 1 + t - 2).choose (s - 1 - 1) ≤ R.card
    · rcases ih (s - 1 + t) (by omega) (s - 1) t (by omega) ht rfl R hR with
        ⟨K, hKR, hKcl, hKcard⟩ | ⟨L, hLB, hLind, hLcard⟩
      · refine Or.inl ⟨insert v K, ?_, ?_, ?_⟩
        · exact Finset.insert_subset_iff.mpr ⟨hv, hKR.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))⟩
        · intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · exact absurd rfl hxy
          · exact (Finset.mem_filter.mp (hKR hy)).2
          · exact (Finset.mem_filter.mp (hKR hx)).2.symm
          · exact hKcl hx hy hxy
        · have hvK : v ∉ K := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp (hKR h)).1).1 rfl
          rw [Finset.card_insert_of_notMem hvK, hKcard]
          omega
      · exact Or.inr ⟨L, hLB.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)), hLind, hLcard⟩
    · have hB : (s + (t - 1) - 2).choose (s - 1) ≤ B.card := by
        have hsub : s - 1 - 1 = s - 2 := by omega
        rw [hsub] at hR
        omega
      rcases ih (s + (t - 1)) (by omega) s (t - 1) hs (by omega) rfl B hB with
        ⟨K, hKB, hKcl, hKcard⟩ | ⟨L, hLB, hLind, hLcard⟩
      · exact Or.inl ⟨K, hKB.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)), hKcl, hKcard⟩
      · refine Or.inr ⟨insert v L, ?_, ?_, ?_⟩
        · exact Finset.insert_subset_iff.mpr ⟨hv, hLB.trans ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))⟩
        · intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · exact absurd rfl hxy
          · exact (Finset.mem_filter.mp (hLB hy)).2
          · exact fun hadj => (Finset.mem_filter.mp (hLB hx)).2 hadj.symm
          · exact hLind hx hy hxy
        · have hvL : v ∉ L := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp (hLB h)).1).1 rfl
          rw [Finset.card_insert_of_notMem hvL, hLcard]
          omega

private lemma choose_le_exp_div (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have h1 : (n.choose k : ℝ) * (k.factorial : ℝ) ≤ (n : ℝ) ^ k := by
    have hnat : n.choose k * k.factorial ≤ n ^ k := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow n k
    exact_mod_cast hnat
  have h2 : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp (k : ℝ) :=
    Real.pow_div_factorial_le_exp (k : ℝ) hkpos.le k
  have h3 : (k : ℝ) ^ k ≤ Real.exp (k : ℝ) * (k.factorial : ℝ) := (div_le_iff₀ hfac_pos).mp h2
  have hexp : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp] at h3
  rw [div_pow, mul_pow, le_div_iff₀ (pow_pos hkpos k)]
  have h4 : (n.choose k : ℝ) * (k : ℝ) ^ k * (k.factorial : ℝ) ≤
      (Real.exp 1) ^ k * (n : ℝ) ^ k * (k.factorial : ℝ) := by
    calc (n.choose k : ℝ) * (k : ℝ) ^ k * (k.factorial : ℝ)
        = ((n.choose k : ℝ) * (k.factorial : ℝ)) * (k : ℝ) ^ k := by ring
      _ ≤ (n : ℝ) ^ k * ((Real.exp 1) ^ k * (k.factorial : ℝ)) :=
          mul_le_mul h1 h3 (pow_nonneg hkpos.le k) (pow_nonneg (Nat.cast_nonneg n) k)
      _ = (Real.exp 1) ^ k * (n : ℝ) ^ k * (k.factorial : ℝ) := by ring
  exact le_of_mul_le_mul_right h4 hfac_pos

private lemma ramsey_symm {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : 2 ≤ U.card) :
    (∃ K ⊆ U, G.IsClique (K : Set V) ∧ Real.log (U.card : ℝ) / 2 ≤ (K.card : ℝ)) ∨
    (∃ L ⊆ U, G.IsIndepSet (L : Set V) ∧ Real.log (U.card : ℝ) / 2 ≤ (L.card : ℝ)) := by
  let s' := Nat.floor (Real.log (U.card : ℝ) / (2 * Real.log 2))
  let s := s' + 1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hUlog_pos : 0 < Real.log (U.card : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < U.card))
  have hchoose_le : (s + s - 2).choose (s - 1) ≤ U.card := by
    have h1 : (s + s - 2).choose (s - 1) ≤ 4 ^ s' := by
      have heq : s + s - 2 = 2 * s' := by omega
      have heq2 : s - 1 = s' := by omega
      rw [heq, heq2]
      calc (2 * s').choose s' ≤ 2 ^ (2 * s') := Nat.choose_le_two_pow _ _
        _ = 4 ^ s' := by rw [pow_mul]; norm_num
    have h2 : (4 : ℝ) ^ s' ≤ (U.card : ℝ) := by
      have hs'_le : (s' : ℝ) ≤ Real.log (U.card : ℝ) / (2 * Real.log 2) :=
        Nat.floor_le (by positivity)
      have h4eq : (4 : ℝ) ^ s' = Real.exp ((s' : ℝ) * (2 * Real.log 2)) := by
        rw [show (4 : ℝ) = Real.exp (2 * Real.log 2) by
          rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]; norm_num]
        rw [← Real.exp_nat_mul]
      rw [h4eq]
      calc Real.exp ((s' : ℝ) * (2 * Real.log 2))
          ≤ Real.exp (Real.log (U.card : ℝ)) := by
              apply Real.exp_le_exp.mpr
              exact (le_div_iff₀ (by positivity)).mp hs'_le
        _ = (U.card : ℝ) := Real.exp_log (by positivity)
    have h1' : (((s + s - 2).choose (s - 1) : ℕ) : ℝ) ≤ (4 : ℝ) ^ s' := by
      exact_mod_cast h1
    exact_mod_cast le_trans h1' h2
  have hs_gt : Real.log (U.card : ℝ) / 2 ≤ (s : ℝ) := by
    have hgt : Real.log (U.card : ℝ) / (2 * Real.log 2) < (s : ℝ) := by
      simpa [s] using Nat.lt_floor_add_one (Real.log (U.card : ℝ) / (2 * Real.log 2))
    have hdiv : Real.log (U.card : ℝ) / 2 ≤ Real.log (U.card : ℝ) / (2 * Real.log 2) := by
      apply div_le_div_of_nonneg_left hUlog_pos.le (by positivity)
      linarith
    linarith
  rcases ramsey_erdos_szekeres G (s + s) s s (by omega) (by omega) rfl U hchoose_le with
    ⟨K, hKU, hKcl, hKcard⟩ | ⟨L, hLU, hLind, hLcard⟩
  · exact Or.inl ⟨K, hKU, hKcl, by rw [hKcard]; exact hs_gt⟩
  · exact Or.inr ⟨L, hLU, hLind, by rw [hLcard]; exact hs_gt⟩

private lemma exp_quarter_le_aux (a : ℝ) (ha0 : 0 < a) (ha4 : a ≤ 1 / 4) :
    Real.exp (1 / (4 * a)) ≤ a * (Real.exp (1 / a - 1) - 1) := by
  set u := 1 / a
  have hu : 4 ≤ u := by
    rw [le_div_iff₀ ha0]
    linarith
  have ha_eq : a = 1 / u := by simp [u]
  have h1 : 1 / (4 * a) = u / 4 := by
    simp only [u]
    field_simp
  rw [h1, ha_eq, one_div_mul_eq_div, le_div_iff₀ (by linarith)]
  have hexp_ge : u + 1 ≤ Real.exp (3 * u / 4 - 1) := by
    have hlin : (3 * u / 4 - 1) ≥ 2 := by linarith
    have htaylor := Real.sum_le_exp_of_nonneg (show 0 ≤ 3 * u / 4 - 1 by linarith) 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
      Nat.cast_ofNat, pow_zero, pow_one, div_one, zero_add] at htaylor
    nlinarith
  have hsplit : Real.exp (u - 1) = Real.exp (u / 4) * Real.exp (3 * u / 4 - 1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpos : 1 ≤ Real.exp (u / 4) := Real.one_le_exp (by linarith)
  rw [hsplit]
  nlinarith

private lemma x_mul_log_mono (Y : ℝ) (hY : 0 ≤ Y) :
    MonotoneOn (fun x : ℝ => x * (1 + Real.log (1 + Y / x))) (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.log
    · exact continuousOn_const.add (continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt hx))
    · intro x hx
      have : 0 ≤ Y / x := div_nonneg hY (le_of_lt hx)
      linarith
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hpos : 0 < 1 + Y / x := by
      have : 0 ≤ Y / x := div_nonneg hY hx0.le
      linarith
    have h1 : HasDerivAt (fun t => 1 + Y / t) (-(Y * (x ^ 2)⁻¹)) x := by
      simpa [div_eq_mul_inv] using (hasDerivAt_const x (1 : ℝ)).fun_add ((hasDerivAt_inv hxne).const_mul Y)
    have h2 : HasDerivAt (fun t => 1 + Real.log (1 + Y / t)) (0 + -(Y * (x ^ 2)⁻¹) / (1 + Y / x)) x :=
      (hasDerivAt_const x (1 : ℝ)).fun_add (h1.log hpos.ne')
    exact ((hasDerivAt_id x).fun_mul h2).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hpos : 0 < 1 + Y / x := by
      have : 0 ≤ Y / x := div_nonneg hY hx0.le
      linarith
    have h1 : HasDerivAt (fun t => 1 + Y / t) (-(Y * (x ^ 2)⁻¹)) x := by
      simpa [div_eq_mul_inv] using (hasDerivAt_const x (1 : ℝ)).fun_add ((hasDerivAt_inv hxne).const_mul Y)
    have h2 : HasDerivAt (fun t => 1 + Real.log (1 + Y / t)) (0 + -(Y * (x ^ 2)⁻¹) / (1 + Y / x)) x :=
      (hasDerivAt_const x (1 : ℝ)).fun_add (h1.log hpos.ne')
    have h3 : HasDerivAt (fun t => t * (1 + Real.log (1 + Y / t)))
        (1 * (1 + Real.log (1 + Y / x)) + x * (0 + -(Y * (x ^ 2)⁻¹) / (1 + Y / x))) x :=
      (hasDerivAt_id x).fun_mul h2
    rw [h3.deriv]
    have hlog_nn : 0 ≤ Real.log (1 + Y / x) := Real.log_nonneg (by
      have : 0 ≤ Y / x := div_nonneg hY hx0.le
      linarith)
    have hfrac : x * (0 + -(Y * (x ^ 2)⁻¹) / (1 + Y / x)) = -(Y / (x + Y)) := by
      have hxY : x + Y ≠ 0 := by linarith
      field_simp
      ring
    rw [hfrac]
    have hle1 : Y / (x + Y) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith

private lemma ramsey_asymm {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : 2 ≤ U.card) (a : ℝ) (ha0 : 0 < a) (ha4 : a ≤ 1 / 4) :
    (∃ K ⊆ U, G.IsClique (K : Set V) ∧ a * Real.log (U.card : ℝ) < (K.card : ℝ)) ∨
    (∃ L ⊆ U, G.IsIndepSet (L : Set V) ∧
      Real.exp (1 / (4 * a)) * Real.log (U.card : ℝ) < (L.card : ℝ)) := by
  have hUlog_pos : 0 < Real.log (U.card : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < U.card))
  let s' := Nat.floor (a * Real.log (U.card : ℝ))
  let t' := Nat.floor (Real.exp (1 / (4 * a)) * Real.log (U.card : ℝ))
  let s := s' + 1
  let t := t' + 1
  have hs_gt : a * Real.log (U.card : ℝ) < (s : ℝ) := by
    simpa [s] using Nat.lt_floor_add_one (a * Real.log (U.card : ℝ))
  have ht_gt : Real.exp (1 / (4 * a)) * Real.log (U.card : ℝ) < (t : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.exp (1 / (4 * a)) * Real.log (U.card : ℝ))
    simpa only [t, Nat.cast_add, Nat.cast_one] using h
  have hchoose_le : (s + t - 2).choose (s - 1) ≤ U.card := by
    have heq1 : s + t - 2 = s' + t' := by omega
    have heq2 : s - 1 = s' := by omega
    rw [heq1, heq2]
    by_cases hs'0 : s' = 0
    · rw [hs'0, Nat.choose_zero_right]
      omega
    have hs'1 : 1 ≤ s' := Nat.pos_of_ne_zero hs'0
    have hs'_pos : (0 : ℝ) < s' := Nat.cast_pos.mpr hs'1
    set X := a * Real.log (U.card : ℝ)
    set Y := a * (Real.exp (1 / a - 1) - 1) * Real.log (U.card : ℝ)
    have hX_pos : 0 < X := by positivity
    have hY_nn : 0 ≤ Y := by
      have := exp_quarter_le_aux a ha0 ha4
      have : 0 < Real.exp (1 / (4 * a)) := Real.exp_pos _
      have : 0 ≤ a * (Real.exp (1 / a - 1) - 1) := by linarith
      positivity
    have hs'_le_X : (s' : ℝ) ≤ X := Nat.floor_le (by positivity)
    have ht'_le_Y : (t' : ℝ) ≤ Y := by
      have h1 : (t' : ℝ) ≤ Real.exp (1 / (4 * a)) * Real.log (U.card : ℝ) :=
        Nat.floor_le (by positivity)
      have h2 := mul_le_mul_of_nonneg_right (exp_quarter_le_aux a ha0 ha4) hUlog_pos.le
      exact le_trans h1 h2
    have hstep1 : (((s' + t').choose s' : ℕ) : ℝ) ≤
        (Real.exp 1 * ((s' : ℝ) + (t' : ℝ)) / (s' : ℝ)) ^ s' := by
      have := choose_le_exp_div (s' + t') s' hs'1
      simpa [Nat.cast_add] using this
    have hstep2 : (Real.exp 1 * ((s' : ℝ) + (t' : ℝ)) / (s' : ℝ)) ^ s' ≤
        (Real.exp 1 * ((s' : ℝ) + Y) / (s' : ℝ)) ^ s' := by
      apply pow_le_pow_left₀ (by positivity)
      gcongr
    have hstep3 : (Real.exp 1 * ((s' : ℝ) + Y) / (s' : ℝ)) ^ s' =
        Real.exp ((s' : ℝ) * (1 + Real.log (1 + Y / (s' : ℝ)))) := by
      have hpos_base : 0 < Real.exp 1 * ((s' : ℝ) + Y) / (s' : ℝ) := by positivity
      have hlog_eq : Real.log (Real.exp 1 * ((s' : ℝ) + Y) / (s' : ℝ)) =
          1 + Real.log (1 + Y / (s' : ℝ)) := by
        have hrew : Real.exp 1 * ((s' : ℝ) + Y) / (s' : ℝ) = Real.exp 1 * (1 + Y / (s' : ℝ)) := by
          field_simp
        rw [hrew, Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
      rw [← Real.exp_log hpos_base, ← Real.exp_nat_mul, hlog_eq]
    have hstep4 : Real.exp ((s' : ℝ) * (1 + Real.log (1 + Y / (s' : ℝ)))) ≤
        Real.exp (X * (1 + Real.log (1 + Y / X))) := by
      apply Real.exp_le_exp.mpr
      exact x_mul_log_mono Y hY_nn hs'_pos hX_pos hs'_le_X
    have hstep5 : X * (1 + Real.log (1 + Y / X)) = Real.log (U.card : ℝ) := by
      have hratio : 1 + Y / X = Real.exp (1 / a - 1) := by
        simp only [X, Y]
        have ha_ne : a ≠ 0 := ha0.ne'
        have hlog_ne : Real.log (U.card : ℝ) ≠ 0 := hUlog_pos.ne'
        field_simp
        ring
      rw [hratio, Real.log_exp]
      simp only [X]
      have ha_ne : a ≠ 0 := ha0.ne'
      field_simp
      ring
    have hfin : (((s' + t').choose s' : ℕ) : ℝ) ≤ (U.card : ℝ) := by
      calc (((s' + t').choose s' : ℕ) : ℝ)
          ≤ (Real.exp 1 * ((s' : ℝ) + (t' : ℝ)) / (s' : ℝ)) ^ s' := hstep1
        _ ≤ (Real.exp 1 * ((s' : ℝ) + Y) / (s' : ℝ)) ^ s' := hstep2
        _ = Real.exp ((s' : ℝ) * (1 + Real.log (1 + Y / (s' : ℝ)))) := hstep3
        _ ≤ Real.exp (X * (1 + Real.log (1 + Y / X))) := hstep4
        _ = Real.exp (Real.log (U.card : ℝ)) := by rw [hstep5]
        _ = (U.card : ℝ) := Real.exp_log (by positivity)
    exact_mod_cast hfin
  rcases ramsey_erdos_szekeres G (s + t) s t (by omega) (by omega) rfl U hchoose_le with
    ⟨K, hKU, hKcl, hKcard⟩ | ⟨L, hLU, hLind, hLcard⟩
  · exact Or.inl ⟨K, hKU, hKcl, by rw [hKcard]; exact hs_gt⟩
  · exact Or.inr ⟨L, hLU, hLind, by rw [hLcard]; exact ht_gt⟩

/- ### Part 3: Weighted Ramsey Lemma (Lemmas 3.2 and 3.3) -/

private lemma two_mul_add_log_one_sub_nonneg (β : ℝ) (h0 : 0 ≤ β) (h34 : β ≤ 3 / 4) :
    0 ≤ 2 * β + Real.log (1 - β) := by
  have h1mβ : 0 < 1 - β := by linarith
  have hexp : 1 ≤ Real.exp (2 * β) * (1 - β) := by
    have htaylor := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * β by linarith) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
      Nat.cast_ofNat, pow_zero, pow_one, div_one, zero_add] at htaylor
    have hpoly : 1 ≤ (1 + 2 * β + (2 * β) ^ 2 / 2 + (2 * β) ^ 3 / 6) * (1 - β) := by
      have hβ2 : β ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by nlinarith
      have hβ3 : β ^ 3 ≤ (3 / 4 : ℝ) ^ 3 := by nlinarith
      have hβ4 : β ^ 4 ≤ (3 / 4 : ℝ) ^ 4 := by nlinarith
      nlinarith
    nlinarith
  have hlog : 0 ≤ Real.log (Real.exp (2 * β) * (1 - β)) := Real.log_nonneg hexp
  rwa [Real.log_mul (Real.exp_ne_zero _) h1mβ.ne', Real.log_exp] at hlog

private lemma weighted_ramsey_one_sum {V : Type*} [DecidableEq V] :
    ∀ n : ℕ, 1 ≤ n →
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V), U.card = n →
      ∀ (r b : V → ℝ),
        (∀ v ∈ U, 0 < r v) → (∀ v ∈ U, 0 < b v) →
        (∀ v ∈ U, r v ≤ b v → Real.log (4 / r v) ≤ b v) →
        (∀ v ∈ U, b v ≤ r v → Real.log (4 / b v) ≤ r v) →
        ∃ K ⊆ U, ∃ L ⊆ U, G.IsClique (K : Set V) ∧ G.IsIndepSet (L : Set V) ∧
          Real.log (n : ℝ) ≤ (∑ v ∈ K, r v) + (∑ v ∈ L, b v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn G _ U hUcard r b hr_pos hb_pos hrb hbr
    -- Helper: if b v ≤ r v then 1 ≤ r v
    have hge_one : ∀ v ∈ U, b v ≤ r v → 1 ≤ r v := by
      intro v hv hle
      by_contra hlt
      push Not at hlt
      have hb1 : b v < 1 := lt_of_le_of_lt hle hlt
      have h4 : Real.exp 1 < 4 / b v := by
        rw [lt_div_iff₀ (hb_pos v hv)]
        have := Real.exp_one_lt_d9
        have := hb_pos v hv
        nlinarith
      have hlog : 1 < Real.log (4 / b v) := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) h4
      linarith [hbr v hv hle]
    by_cases hn1 : n = 1
    · subst hn1
      refine ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, by simp, by simp, ?_⟩
      simp
    by_cases hn2 : n = 2
    · subst hn2
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
      have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
      rcases le_total (b v) (r v) with hle | hle
      · refine ⟨{v}, Finset.singleton_subset_iff.mpr hv, ∅, Finset.empty_subset _,
          by simp, by simp, ?_⟩
        simp only [Finset.sum_singleton, Finset.sum_empty, add_zero, Nat.cast_ofNat]
        linarith [hge_one v hv hle]
      · have hbv : 1 ≤ b v := by
          by_contra hlt
          push Not at hlt
          have hr1 : r v < 1 := lt_of_le_of_lt hle hlt
          have h4 : Real.exp 1 < 4 / r v := by
            rw [lt_div_iff₀ (hr_pos v hv)]
            have := Real.exp_one_lt_d9
            have := hr_pos v hv
            nlinarith
          have hlog : 1 < Real.log (4 / r v) := by
            rw [← Real.log_exp 1]
            exact Real.log_lt_log (Real.exp_pos 1) h4
          linarith [hrb v hv hle]
        refine ⟨∅, Finset.empty_subset _, {v}, Finset.singleton_subset_iff.mpr hv,
          by simp, by simp, ?_⟩
        simp only [Finset.sum_empty, Finset.sum_singleton, zero_add, Nat.cast_ofNat]
        linarith
    have hn3 : 3 ≤ n := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
    -- Step lemma for the case b v ≤ r v (we apply it either to G or to Gᶜ)
    have hstep : ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (r' b' : V → ℝ),
        (∀ x ∈ U, 0 < r' x) → (∀ x ∈ U, 0 < b' x) →
        (∀ x ∈ U, r' x ≤ b' x → Real.log (4 / r' x) ≤ b' x) →
        (∀ x ∈ U, b' x ≤ r' x → Real.log (4 / b' x) ≤ r' x) →
        b' v ≤ r' v →
        ∃ K ⊆ U, ∃ L ⊆ U, H.IsClique (K : Set V) ∧ H.IsIndepSet (L : Set V) ∧
          Real.log (n : ℝ) ≤ (∑ x ∈ K, r' x) + (∑ x ∈ L, b' x) := by
      intro H _ r' b' hr' hb' hrb' hbr' hbv_le
      have hrv1 : 1 ≤ r' v := by
        by_contra hlt
        push Not at hlt
        have hb1 : b' v < 1 := lt_of_le_of_lt hbv_le hlt
        have h4 : Real.exp 1 < 4 / b' v := by
          rw [lt_div_iff₀ (hb' v hv)]
          have := Real.exp_one_lt_d9
          have := hb' v hv
          nlinarith
        have hlog : 1 < Real.log (4 / b' v) := by
          rw [← Real.log_exp 1]
          exact Real.log_lt_log (Real.exp_pos 1) h4
        linarith [hbr' v hv hbv_le]
      by_cases hrv_big : Real.log (n : ℝ) ≤ r' v
      · refine ⟨{v}, Finset.singleton_subset_iff.mpr hv, ∅, Finset.empty_subset _,
          by simp, by simp, ?_⟩
        simpa using hrv_big
      push Not at hrv_big
      have hbv_gt : 4 / (n : ℝ) < b' v := by
        have hlog_lt : Real.log (4 / b' v) < Real.log (n : ℝ) :=
          lt_of_le_of_lt (hbr' v hv hbv_le) hrv_big
        have h4lt : 4 / b' v < (n : ℝ) := by
          by_contra hge
          push Not at hge
          have := Real.log_le_log (by positivity) hge
          linarith
        rw [div_lt_iff₀ (hb' v hv)] at h4lt
        rw [div_lt_iff₀ (by positivity)]
        linarith
      let R := (U.erase v).filter (fun w => H.Adj v w)
      let B := (U.erase v).filter (fun w => ¬ H.Adj v w)
      have hRU : R ⊆ U := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hBU : B ⊆ U := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hRB : R.card + B.card = n - 1 := by
        rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv, hUcard]
      have hn_pos : (0 : ℝ) < n := by positivity
      -- Subcase: R is nonempty and 0 ≤ r' v + log (R.card / n)
      by_cases hRcase : 0 < R.card ∧ 0 ≤ r' v + Real.log ((R.card : ℝ) / n)
      · obtain ⟨hRpos, hRlog⟩ := hRcase
        have hRlt : R.card < n := by omega
        obtain ⟨K, hKR, L, hLR, hKcl, hLind, hsum⟩ :=
          ih R.card hRlt hRpos H R rfl r' b'
            (fun x hx => hr' x (hRU hx)) (fun x hx => hb' x (hRU hx))
            (fun x hx => hrb' x (hRU hx)) (fun x hx => hbr' x (hRU hx))
        have hvK : v ∉ K := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp (hKR h)).1).1 rfl
        refine ⟨insert v K, Finset.insert_subset_iff.mpr ⟨hv, hKR.trans hRU⟩,
          L, hLR.trans hRU, ?_, hLind, ?_⟩
        · intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · exact absurd rfl hxy
          · exact (Finset.mem_filter.mp (hKR hy)).2
          · exact (Finset.mem_filter.mp (hKR hx)).2.symm
          · exact hKcl hx hy hxy
        · rw [Finset.sum_insert hvK]
          have hlog_split : Real.log ((R.card : ℝ) / n) = Real.log (R.card : ℝ) - Real.log (n : ℝ) :=
            Real.log_div (Nat.cast_ne_zero.mpr hRpos.ne') hn_pos.ne'
          linarith
      · -- Otherwise use B!
        set α : ℝ := (R.card : ℝ) / n
        have hα_nn : 0 ≤ α := by positivity
        have hα_bound : α ≤ b' v / 4 ∧ α ≤ Real.exp (-1) := by
          by_cases hR0 : R.card = 0
          · simp only [α, hR0, Nat.cast_zero, zero_div]
            exact ⟨div_nonneg (hb' v hv).le (by norm_num), (Real.exp_pos _).le⟩
          · have hRpos : 0 < R.card := Nat.pos_of_ne_zero hR0
            have hneg : r' v + Real.log α < 0 := by
              by_contra hge
              push Not at hge
              exact hRcase ⟨hRpos, hge⟩
            have hα_pos : 0 < α := by positivity
            have hα_lt_exp : α < Real.exp (-r' v) := by
              rw [← Real.log_lt_iff_lt_exp hα_pos]
              linarith
            have h1 : α ≤ b' v / 4 := by
              have hle : Real.exp (-r' v) ≤ b' v / 4 := by
                have hlog := hbr' v hv hbv_le
                have hneg_log : -r' v ≤ Real.log (b' v / 4) := by
                  rw [Real.log_div (hb' v hv).ne' (by norm_num)]
                  rw [Real.log_div (by norm_num) (hb' v hv).ne'] at hlog
                  linarith
                calc Real.exp (-r' v) ≤ Real.exp (Real.log (b' v / 4)) := Real.exp_le_exp.mpr hneg_log
                  _ = b' v / 4 := Real.exp_log (div_pos (hb' v hv) (by norm_num))
              linarith
            have h2 : α ≤ Real.exp (-1) :=
              le_trans hα_lt_exp.le (Real.exp_le_exp.mpr (by linarith))
            exact ⟨h1, h2⟩
        set β : ℝ := α + 1 / (n : ℝ)
        have hβ0 : 0 ≤ β := by positivity
        have hβ34 : β ≤ 3 / 4 := by
          have hexp_m1 : Real.exp (-1) ≤ 2 / 5 := by
            rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
            have := Real.exp_one_gt_d9
            linarith
          have hn3_r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
          have h1n : 1 / (n : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hn3_r
          linarith [hα_bound.2]
        have hB_cast : (B.card : ℝ) = (n : ℝ) * (1 - β) := by
          have hBnat : (B.card : ℝ) = (n : ℝ) - 1 - (R.card : ℝ) := by
            have : B.card + R.card + 1 = n := by omega
            have : (B.card : ℝ) + (R.card : ℝ) + 1 = (n : ℝ) := by exact_mod_cast this
            linarith
          simp only [β, α]
          rw [hBnat]
          field_simp
          ring
        have hBpos : 0 < B.card := by
          have : (0 : ℝ) < (B.card : ℝ) := by
            rw [hB_cast]
            have : 0 < 1 - β := by linarith
            positivity
          exact_mod_cast this
        have hBlt : B.card < n := by omega
        have hbv_ge_2β : 2 * β ≤ b' v := by
          simp only [β]
          have h4n : 4 * (1 / (n : ℝ)) < b' v := by
            have : 4 * (1 / (n : ℝ)) = 4 / (n : ℝ) := by ring
            linarith
          linarith [hα_bound.1, h4n]
        obtain ⟨K, hKB, L, hLB, hKcl, hLind, hsum⟩ :=
          ih B.card hBlt hBpos H B rfl r' b'
            (fun x hx => hr' x (hBU hx)) (fun x hx => hb' x (hBU hx))
            (fun x hx => hrb' x (hBU hx)) (fun x hx => hbr' x (hBU hx))
        have hvL : v ∉ L := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp (hLB h)).1).1 rfl
        refine ⟨K, hKB.trans hBU, insert v L, Finset.insert_subset_iff.mpr ⟨hv, hLB.trans hBU⟩,
          hKcl, ?_, ?_⟩
        · intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · exact absurd rfl hxy
          · exact (Finset.mem_filter.mp (hLB hy)).2
          · exact fun hadj => (Finset.mem_filter.mp (hLB hx)).2 hadj.symm
          · exact hLind hx hy hxy
        · rw [Finset.sum_insert hvL]
          have hlogB : Real.log (B.card : ℝ) = Real.log (n : ℝ) + Real.log (1 - β) := by
            rw [hB_cast, Real.log_mul hn_pos.ne' (by linarith)]
          have haux := two_mul_add_log_one_sub_nonneg β hβ0 hβ34
          linarith
    rcases le_total (b v) (r v) with hle | hle
    · exact hstep G r b hr_pos hb_pos hrb hbr hle
    · -- Swap G with Gᶜ and r with b
      obtain ⟨K, hKU, L, hLU, hKcl, hLind, hsum⟩ :=
        hstep Gᶜ b r hb_pos hr_pos hbr hrb hle
      refine ⟨L, hLU, K, hKU, ?_, ?_, by linarith⟩
      · intro x hx y hy hxy
        have hnot := hLind hx hy hxy
        simp only [SimpleGraph.compl_adj, not_and, not_not] at hnot
        exact hnot hxy
      · intro x hx y hy hxy
        exact (hKcl hx hy hxy).2

private lemma weighted_ramsey {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : U.Nonempty) (c : ℝ) (hc : 0 < c) (r b : V → ℝ)
    (hr : ∀ v ∈ U, 0 < r v) (hb : ∀ v ∈ U, 0 < b v)
    (hrb : ∀ v ∈ U, r v ≤ b v → c * Real.log (4 * c / r v) ≤ b v)
    (hbr : ∀ v ∈ U, b v ≤ r v → c * Real.log (4 * c / b v) ≤ r v) :
    (∃ K ⊆ U, G.IsClique (K : Set V) ∧ c / 2 * Real.log (U.card : ℝ) ≤ ∑ v ∈ K, r v) ∨
    (∃ L ⊆ U, G.IsIndepSet (L : Set V) ∧ c / 2 * Real.log (U.card : ℝ) ≤ ∑ v ∈ L, b v) := by
  obtain ⟨K, hKU, L, hLU, hKcl, hLind, hsum⟩ :=
    weighted_ramsey_one_sum U.card hU.card_pos G U rfl (fun v => r v / c) (fun v => b v / c)
      (fun v hv => div_pos (hr v hv) hc) (fun v hv => div_pos (hb v hv) hc)
      (fun v hv hle => by
        have hle' : r v ≤ b v := (div_le_div_iff_of_pos_right hc).mp hle
        rw [show 4 / (r v / c) = 4 * c / r v by field_simp]
        exact (le_div_iff₀ hc).mpr (by linarith [hrb v hv hle']))
      (fun v hv hle => by
        have hle' : b v ≤ r v := (div_le_div_iff_of_pos_right hc).mp hle
        rw [show 4 / (b v / c) = 4 * c / b v by field_simp]
        exact (le_div_iff₀ hc).mpr (by linarith [hbr v hv hle']))
  rw [← Finset.sum_div, ← Finset.sum_div, ← add_div, le_div_iff₀ hc] at hsum
  by_cases hK : c / 2 * Real.log (U.card : ℝ) ≤ ∑ v ∈ K, r v
  · exact Or.inl ⟨K, hKU, hKcl, hK⟩
  · exact Or.inr ⟨L, hLU, hLind, by linarith⟩

/- ### Part 4: Nested Induction and Main Theorem (Conlon-Fox-Sudakov Theorem 3.1) -/

private lemma log_le_sqrt_mul_two (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsq
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (by linarith)]
    ring
  linarith

private lemma exp_ge_pow_six_div (x : ℝ) (hx : 0 ≤ x) : x ^ 6 / 720 ≤ Real.exp x := by
  have ht := Real.sum_le_exp_of_nonneg hx 7
  have hterm : x ^ 6 / (Nat.factorial 6 : ℝ) ≤ ∑ i ∈ Finset.range 7, x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (by norm_num))
  have hfac : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hfac] at hterm
  linarith

set_option maxHeartbeats 1200000 in
private lemma inner_drc_induction {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (L : ℝ) (hL : 10000 ≤ L) (scale : ℕ → ℕ)
    (hscale_ge : ∀ i < d, 100 ≤ scale i)
    (hscale_log_lb : ∀ i < d, 100 * Real.sqrt L ≤ Real.log (scale i : ℝ))
    (hscale_ratio : ∀ j k, j < k → k < d →
      (1 / 2 : ℝ) * Real.exp (Real.sqrt L) * Real.log (scale j : ℝ) ≤ Real.log (scale k : ℝ))
    (hd_le : (d : ℝ) ≤ Real.sqrt L / 2)
    (j : ℕ) (hj : j < d)
    (S_cur : ∀ i : Fin d, Finset V)
    (hSj_le : (S_cur ⟨j, hj⟩).card ≤ scale j)
    (hS_lb : ∀ i : Fin d, j ≤ i.val →
      (scale i.val : ℝ) ^ (1 - (j : ℝ) / (2 * ((i.val : ℝ) + 1))) ≤ ((S_cur i).card : ℝ)) :
    let sqL := Real.sqrt L
    let s := Nat.ceil (Real.log (scale j : ℝ) * Real.log L)
    let t := Nat.ceil (Real.log (scale j : ℝ) / (4 * sqL))
    ∃ (T : Finset V) (χ : Fin d → Bool),
      T ⊆ S_cur ⟨j, hj⟩ ∧
      (scale j : ℝ) ^ (1 / 4 : ℝ) ≤ (T.card : ℝ) ∧
      ∀ (k : Fin d), j < k.val →
        ∀ A ⊆ T, A.card = s →
          (scale k.val : ℝ) ^ (1 - ((j : ℝ) + 1) / (2 * ((k.val : ℝ) + 1))) ≤
            (((S_cur k).filter (fun v => ∀ u ∈ A,
              if χ k then G.Adj u v else ¬ G.Adj u v)).card : ℝ) := by
  intro sqL s t
  have hsqL : 100 ≤ sqL := by
    have : Real.sqrt 10000 ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
    have h100 : Real.sqrt 10000 = 100 := by
      rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hsqL_sq : sqL ^ 2 = L := Real.sq_sqrt (by linarith)
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by linarith)
  have hlogL_le : Real.log L ≤ 2 * sqL := log_le_sqrt_mul_two L (by linarith)
  have hlog_sj_pos : 0 < Real.log (scale j : ℝ) := by
    have := hscale_log_lb j hj; linarith
  have hs_pos : 1 ≤ s := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (mul_pos hlog_sj_pos hlogL_pos)).ne'
  have ht_pos : 1 ≤ t := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (div_pos hlog_sj_pos (by linarith))).ne'
  -- Auxiliary induction on r from 0 to d - 1 - j
  have hrec : ∀ r : ℕ, j + r < d →
      ∃ (T : Finset V) (χ : Fin d → Bool),
        T ⊆ S_cur ⟨j, hj⟩ ∧
        ((1 / 2 : ℝ) ^ (t + 1)) ^ r * ((S_cur ⟨j, hj⟩).card : ℝ) ≤ (T.card : ℝ) ∧
        ∀ (k : Fin d), j < k.val → k.val ≤ j + r →
          ∀ A ⊆ T, A.card = s →
            (scale k.val : ℝ) ^ (1 - ((j : ℝ) + 1) / (2 * ((k.val : ℝ) + 1))) ≤
              (((S_cur k).filter (fun v => ∀ u ∈ A,
                if χ k then G.Adj u v else ¬ G.Adj u v)).card : ℝ) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨S_cur ⟨j, hj⟩, fun _ => true, Finset.Subset.refl _, by simp, ?_⟩
      intro k hjk hk
      omega
    | succ r ih =>
      intro hjr
      obtain ⟨T, χ, hTS, hTcard, hTprop⟩ := ih (by omega)
      let k : Fin d := ⟨j + r + 1, hjr⟩
      have hjk : j < k.val := Nat.lt_add_of_pos_right (Nat.succ_pos r)
      have hkd : k.val < d := k.isLt
      have hSj_lb : (scale j : ℝ) ^ (1 / 2 : ℝ) ≤ ((S_cur ⟨j, hj⟩).card : ℝ) := by
        have h1 := hS_lb ⟨j, hj⟩ le_rfl
        have hexp : (1 / 2 : ℝ) ≤ 1 - (j : ℝ) / (2 * ((j : ℝ) + 1)) := by
          have : (j : ℝ) / (2 * ((j : ℝ) + 1)) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
          linarith
        exact le_trans (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (by have := hscale_ge j hj; omega : 1 ≤ scale j)) hexp) h1
      -- Show T is nonempty via the lower bound on ((1/2)^(t+1))^r * |S_cur j|
      have hT_lb_quarter : (scale j : ℝ) ^ (1 / 4 : ℝ) ≤ (T.card : ℝ) := by
        have hr_le_d : (r : ℝ) ≤ d := by exact_mod_cast (by omega : r ≤ d)
        have ht_ub : (t : ℝ) ≤ Real.log (scale j : ℝ) / (4 * sqL) + 1 :=
          (Nat.ceil_lt_add_one (div_nonneg hlog_sj_pos.le (by linarith))).le
        have hlog2_lt : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hshrink : (scale j : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ((1 / 2 : ℝ) ^ (t + 1)) ^ r := by
          rw [← pow_mul]
          have hpos2 : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
          rw [show (1 / 2 : ℝ) ^ ((t + 1) * r) = Real.exp (-(((t + 1) * r : ℕ) : ℝ) * Real.log 2) by
            rw [← Real.exp_log hpos2, ← Real.exp_nat_mul]
            congr 1
            rw [one_div, Real.log_inv]
            ring]
          rw [Real.rpow_def_of_pos (by exact_mod_cast (by have := hscale_ge j hj; omega : 0 < scale j))]
          apply Real.exp_le_exp.mpr
          have h1 : (((t + 1) * r : ℕ) : ℝ) = ((t : ℝ) + 1) * (r : ℝ) := by push_cast; ring
          rw [h1]
          have h2 : ((t : ℝ) + 1) * (r : ℝ) ≤ (Real.log (scale j : ℝ) / (4 * sqL) + 2) * (sqL / 2) := by
            apply mul_le_mul (by linarith) (le_trans hr_le_d hd_le) (Nat.cast_nonneg r) (by positivity)
          have h3 : (Real.log (scale j : ℝ) / (4 * sqL) + 2) * (sqL / 2) =
              Real.log (scale j : ℝ) / 8 + sqL := by
            have : sqL ≠ 0 := by linarith
            field_simp
            ring
          have h4 : sqL ≤ Real.log (scale j : ℝ) / 100 := by
            have := hscale_log_lb j hj; linarith
          have h5 : ((t : ℝ) + 1) * (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log (scale j : ℝ) := by linarith
          nlinarith
        have hmul := mul_le_mul hshrink hSj_lb (by positivity) (by positivity)
        have hcomb : (scale j : ℝ) ^ (-(1 / 4 : ℝ)) * (scale j : ℝ) ^ (1 / 2 : ℝ) =
            (scale j : ℝ) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add (by exact_mod_cast (by have := hscale_ge j hj; omega : 0 < scale j))]
          norm_num
        linarith
      have hT_ne : T.Nonempty := Finset.card_pos.mp (by
        have h1 : (1 : ℝ) ≤ (scale j : ℝ) ^ (1 / 4 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast (by have := hscale_ge j hj; omega : 1 ≤ scale j)) (by norm_num)
        have : (0 : ℝ) < (T.card : ℝ) := lt_of_lt_of_le (by norm_num) (le_trans h1 hT_lb_quarter)
        exact_mod_cast this)
      have hSk_lb : (scale k.val : ℝ) ^ (1 / 2 : ℝ) ≤ ((S_cur k).card : ℝ) := by
        have h1 := hS_lb k (by omega)
        have hexp : (1 / 2 : ℝ) ≤ 1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1)) := by
          have : (j : ℝ) / (2 * ((k.val : ℝ) + 1)) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            have : (j : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast hjk.le
            linarith
          linarith
        exact le_trans (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (by have := hscale_ge k.val hkd; omega : 1 ≤ scale k.val)) hexp) h1
      have hSk_ne : (S_cur k).Nonempty := Finset.card_pos.mp (by
        have h1 : (1 : ℝ) ≤ (scale k.val : ℝ) ^ (1 / 2 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast (by have := hscale_ge k.val hkd; omega : 1 ≤ scale k.val)) (by norm_num)
        have : (0 : ℝ) < ((S_cur k).card : ℝ) := lt_of_lt_of_le (by norm_num) (le_trans h1 hSk_lb)
        exact_mod_cast this)
      -- Choose majority color c_k between T and S_cur k
      have hsum_split : (∑ u ∈ T, (((S_cur k).filter (fun v => G.Adj u v)).card : ℝ)) +
          (∑ u ∈ T, (((S_cur k).filter (fun v => ¬ G.Adj u v)).card : ℝ)) =
          (T.card : ℝ) * ((S_cur k).card : ℝ) := by
        rw [← Finset.sum_add_distrib]
        have : ∀ u ∈ T, (((S_cur k).filter (fun v => G.Adj u v)).card : ℝ) +
            (((S_cur k).filter (fun v => ¬ G.Adj u v)).card : ℝ) = ((S_cur k).card : ℝ) := by
          intro u _
          exact_mod_cast Finset.card_filter_add_card_filter_not (s := S_cur k) (p := fun v => G.Adj u v)
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      let c_k : Bool := decide ((1 / 2 : ℝ) * (T.card : ℝ) * ((S_cur k).card : ℝ) ≤
        ∑ u ∈ T, (((S_cur k).filter (fun v => G.Adj u v)).card : ℝ))
      let E : V → V → Prop := fun u v => if c_k then G.Adj u v else ¬ G.Adj u v
      have hedges : (1 / 2 : ℝ) * (T.card : ℝ) * ((S_cur k).card : ℝ) ≤
          ∑ u ∈ T, (((S_cur k).filter (fun v => E u v)).card : ℝ) := by
        by_cases hmaj : (1 / 2 : ℝ) * (T.card : ℝ) * ((S_cur k).card : ℝ) ≤
            ∑ u ∈ T, (((S_cur k).filter (fun v => G.Adj u v)).card : ℝ)
        · have hck : c_k = true := decide_eq_true hmaj
          simpa [E, hck] using hmaj
        · have hck : c_k = false := decide_eq_false hmaj
          simp only [E, hck, Bool.false_eq_true, ↓reduceIte]
          linarith
      -- Set m = floor(|S_cur k|^(1 - 1/(2*sqL)))
      let m := Nat.floor (((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL)))
      have hSk_pos : (0 : ℝ) < ((S_cur k).card : ℝ) := Nat.cast_pos.mpr hSk_ne.card_pos
      have hT_pos : (0 : ℝ) < (T.card : ℝ) := Nat.cast_pos.mpr hT_ne.card_pos
      have hT_le_sj : (T.card : ℝ) ≤ (scale j : ℝ) := by
        exact_mod_cast le_trans (Finset.card_le_card hTS) hSj_le
      have hlog_Sk_lb : (1 / 2 : ℝ) * Real.log (scale k.val : ℝ) ≤ Real.log ((S_cur k).card : ℝ) := by
        have hsk_pos : (0 : ℝ) < (scale k.val : ℝ) := by
          exact_mod_cast (by have := hscale_ge k.val hkd; omega : 0 < scale k.val)
        have h1 := Real.log_le_log (Real.rpow_pos_of_pos hsk_pos _) hSk_lb
        rwa [Real.log_rpow hsk_pos] at h1
      -- Verify DRC condition
      have hcond : (T.card.choose s : ℝ) * ((m : ℝ) / ((S_cur k).card : ℝ)) ^ t ≤
          (1 / 2 : ℝ) ^ t * (T.card : ℝ) / 2 := by
        by_cases hm0 : m = 0
        · rw [hm0, Nat.cast_zero, zero_div, zero_pow (by omega : t ≠ 0), mul_zero]
          positivity
        have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
        have hsj_pos : (0 : ℝ) < (scale j : ℝ) := by
          exact_mod_cast (by have := hscale_ge j hj; omega : 0 < scale j)
        have hchoose_le : (T.card.choose s : ℝ) ≤ (scale j : ℝ) ^ s := by
          have h1 : T.card.choose s ≤ T.card ^ s := by
            calc T.card.choose s ≤ T.card.choose s * s.factorial :=
                  Nat.le_mul_of_pos_right _ (Nat.factorial_pos s)
              _ = T.card.descFactorial s := by rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
              _ ≤ T.card ^ s := Nat.descFactorial_le_pow T.card s
          have h1' : (T.card.choose s : ℝ) ≤ (T.card : ℝ) ^ s := by exact_mod_cast h1
          exact le_trans h1' (pow_le_pow_left₀ hT_pos.le hT_le_sj s)
        -- Suffices (scale j)^s * (2 * m / |S_cur k|)^t ≤ 1/2
        have hmain : (scale j : ℝ) ^ s * (2 * (m : ℝ) / ((S_cur k).card : ℝ)) ^ t ≤ 1 / 2 := by
          have hLHS_pos : 0 < (scale j : ℝ) ^ s * (2 * (m : ℝ) / ((S_cur k).card : ℝ)) ^ t := by
            positivity
          rw [← Real.exp_log hLHS_pos]
          have hlog_ub : Real.log ((scale j : ℝ) ^ s * (2 * (m : ℝ) / ((S_cur k).card : ℝ)) ^ t) ≤ -1 := by
            rw [Real.log_mul (pow_ne_zero s hsj_pos.ne') (pow_ne_zero t (by positivity)),
              Real.log_pow, Real.log_pow]
            have hm_le : (m : ℝ) ≤ ((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL)) :=
              Nat.floor_le (by positivity)
            have hlog_m_div : Real.log (2 * (m : ℝ) / ((S_cur k).card : ℝ)) ≤
                Real.log 2 - (1 / (2 * sqL)) * Real.log ((S_cur k).card : ℝ) := by
              rw [mul_div_assoc, Real.log_mul (by norm_num) (by positivity)]
              have hdiv_le : (m : ℝ) / ((S_cur k).card : ℝ) ≤ ((S_cur k).card : ℝ) ^ (-(1 / (2 * sqL))) := by
                rw [div_le_iff₀ hSk_pos]
                calc (m : ℝ) ≤ ((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL)) := hm_le
                  _ = ((S_cur k).card : ℝ) ^ (-(1 / (2 * sqL))) * ((S_cur k).card : ℝ) := by
                      rw [← Real.rpow_add_one hSk_pos.ne']
                      congr 1; ring
              have hlog_d := Real.log_le_log (by positivity) hdiv_le
              rw [Real.log_rpow hSk_pos] at hlog_d
              linarith
            have ht_lb : Real.log (scale j : ℝ) / (4 * sqL) ≤ (t : ℝ) := Nat.le_ceil _
            have ht_ub : (t : ℝ) ≤ Real.log (scale j : ℝ) / (4 * sqL) + 1 :=
              (Nat.ceil_lt_add_one (div_nonneg hlog_sj_pos.le (by linarith))).le
            have hs_ub : (s : ℝ) ≤ Real.log (scale j : ℝ) * Real.log L + 1 :=
              (Nat.ceil_lt_add_one (mul_nonneg hlog_sj_pos.le hlogL_pos.le)).le
            have hlog_Sk_sj : (1 / 4 : ℝ) * Real.exp sqL * Real.log (scale j : ℝ) ≤
                Real.log ((S_cur k).card : ℝ) := by
              have hr := hscale_ratio j k.val hjk hkd
              linarith
            have hneg_term : (Real.exp sqL / (32 * L)) * (Real.log (scale j : ℝ)) ^ 2 ≤
                (t : ℝ) * ((1 / (2 * sqL)) * Real.log ((S_cur k).card : ℝ)) := by
              have h1 : (Real.log (scale j : ℝ) / (4 * sqL)) *
                  ((1 / (2 * sqL)) * ((1 / 4 : ℝ) * Real.exp sqL * Real.log (scale j : ℝ))) ≤
                  (t : ℝ) * ((1 / (2 * sqL)) * Real.log ((S_cur k).card : ℝ)) := by
                apply mul_le_mul ht_lb
                  (mul_le_mul_of_nonneg_left hlog_Sk_sj (by positivity))
                  (by positivity) (Nat.cast_nonneg t)
              have h2 : (Real.log (scale j : ℝ) / (4 * sqL)) *
                  ((1 / (2 * sqL)) * ((1 / 4 : ℝ) * Real.exp sqL * Real.log (scale j : ℝ))) =
                  (Real.exp sqL / (32 * L)) * (Real.log (scale j : ℝ)) ^ 2 := by
                have hsq_ne : sqL ≠ 0 := by linarith
                have hL_ne : L ≠ 0 := by linarith
                rw [← hsqL_sq]
                field_simp
                ring
              linarith
            have hexp_big : 10 * sqL ≤ Real.exp sqL / (32 * L) := by
              have h6 := exp_ge_pow_six_div sqL (by linarith)
              rw [le_div_iff₀ (by linarith), ← hsqL_sq]
              have hsq3 : (100 : ℝ) ^ 3 ≤ sqL ^ 3 := pow_le_pow_left₀ (by norm_num) hsqL 3
              have hsq6 : sqL ^ 6 = sqL ^ 3 * sqL ^ 3 := by ring
              have hprod : 320 * sqL ^ 3 * 720 ≤ sqL ^ 3 * sqL ^ 3 := by
                have h3 : (230400 : ℝ) ≤ sqL ^ 3 := by norm_num at hsq3; linarith
                have hpos3 : (0 : ℝ) ≤ sqL ^ 3 := by positivity
                nlinarith
              linarith
            have hlog2_le1 : Real.log 2 ≤ 1 := (lt_trans Real.log_two_lt_d9 (by norm_num)).le
            have hpos_part : (s : ℝ) * Real.log (scale j : ℝ) + (t : ℝ) * Real.log 2 ≤
                (3 * sqL) * (Real.log (scale j : ℝ)) ^ 2 := by
              have h1 : (s : ℝ) * Real.log (scale j : ℝ) ≤
                  (Real.log (scale j : ℝ) * Real.log L + 1) * Real.log (scale j : ℝ) :=
                mul_le_mul_of_nonneg_right hs_ub hlog_sj_pos.le
              have h2 : (t : ℝ) * Real.log 2 ≤ Real.log (scale j : ℝ) / (4 * sqL) + 1 := by
                nlinarith
              have h3 : 4 * sqL ≤ Real.log (scale j : ℝ) := by
                have := hscale_log_lb j hj; linarith
              have h4 : Real.log (scale j : ℝ) / (4 * sqL) ≤ Real.log (scale j : ℝ) := by
                rw [div_le_iff₀ (by linarith)]
                nlinarith
              nlinarith
            have htmul : (t : ℝ) * Real.log (2 * (m : ℝ) / ((S_cur k).card : ℝ)) ≤
                (t : ℝ) * Real.log 2 - (t : ℝ) * ((1 / (2 * sqL)) * Real.log ((S_cur k).card : ℝ)) := by
              have := mul_le_mul_of_nonneg_left hlog_m_div (Nat.cast_nonneg t)
              linarith
            have hsq_ge1 : (1 : ℝ) ≤ (Real.log (scale j : ℝ)) ^ 2 := by
              have := hscale_log_lb j hj; nlinarith
            nlinarith
          calc Real.exp (Real.log ((scale j : ℝ) ^ s * (2 * (m : ℝ) / ((S_cur k).card : ℝ)) ^ t))
              ≤ Real.exp (-1) := Real.exp_le_exp.mpr hlog_ub
            _ ≤ 1 / 2 := by
              rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
              have := Real.exp_one_gt_d9; linarith
        have h1 : (T.card.choose s : ℝ) * ((m : ℝ) / ((S_cur k).card : ℝ)) ^ t ≤
            (1 / 2 : ℝ) ^ t * ((scale j : ℝ) ^ s * (2 * (m : ℝ) / ((S_cur k).card : ℝ)) ^ t) := by
          have hrew : (1 / 2 : ℝ) ^ t * ((scale j : ℝ) ^ s * (2 * (m : ℝ) / ((S_cur k).card : ℝ)) ^ t) =
              (scale j : ℝ) ^ s * ((m : ℝ) / ((S_cur k).card : ℝ)) ^ t := by
            rw [mul_comm ((1 / 2 : ℝ) ^ t), mul_assoc, ← mul_pow]
            congr 2; ring
          rw [hrew]
          exact mul_le_mul_of_nonneg_right hchoose_le (by positivity)
        have hT1 : (1 : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hT_ne.card_pos
        calc (T.card.choose s : ℝ) * ((m : ℝ) / ((S_cur k).card : ℝ)) ^ t
            ≤ (1 / 2 : ℝ) ^ t * ((scale j : ℝ) ^ s * (2 * (m : ℝ) / ((S_cur k).card : ℝ)) ^ t) := h1
          _ ≤ (1 / 2 : ℝ) ^ t * (1 / 2) := mul_le_mul_of_nonneg_left hmain (by positivity)
          _ ≤ (1 / 2 : ℝ) ^ t * (T.card : ℝ) / 2 := by
              have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ t := by positivity
              nlinarith
      -- Apply DRC
      obtain ⟨T', hT'T, hT'card, hT'prop⟩ := dependent_random_choice T (S_cur k) hT_ne hSk_ne E
        (1 / 2) (by norm_num) s t m hs_pos ht_pos hedges hcond
      -- Lower bound on m
      have hm_lb : (scale k.val : ℝ) ^ (1 - ((j : ℝ) + 1) / (2 * ((k.val : ℝ) + 1))) ≤ (m : ℝ) := by
        have hSk_exp_ge : (2 : ℝ) ≤ ((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL)) := by
          have hlog_ge : Real.log 2 ≤ (1 - 1 / (2 * sqL)) * Real.log ((S_cur k).card : ℝ) := by
            have h1 : 4 * sqL ≤ Real.log (scale k.val : ℝ) := by
              have := hscale_log_lb k.val hkd; linarith
            have h2 : 2 * sqL ≤ Real.log ((S_cur k).card : ℝ) := by linarith
            have h3 : (1 / 2 : ℝ) ≤ 1 - 1 / (2 * sqL) := by
              have : 1 / (2 * sqL) ≤ 1 / 2 := by
                rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
              linarith
            have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
            nlinarith
          calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
            _ ≤ Real.exp (Real.log ((S_cur k).card : ℝ) * (1 - 1 / (2 * sqL))) :=
                Real.exp_le_exp.mpr (by rw [mul_comm]; exact hlog_ge)
            _ = ((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL)) :=
                (Real.rpow_def_of_pos hSk_pos _).symm
        have hm_half : (1 / 2 : ℝ) * ((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL)) ≤ (m : ℝ) := by
          have hfl := Nat.sub_one_lt_floor (((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL)))
          linarith
        have hlog_target : (1 - ((j : ℝ) + 1) / (2 * ((k.val : ℝ) + 1))) * Real.log (scale k.val : ℝ) ≤
            Real.log ((1 / 2 : ℝ) * ((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL))) := by
          rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hSk_pos _).ne', Real.log_rpow hSk_pos]
          have hsk_pos : (0 : ℝ) < (scale k.val : ℝ) := by
            exact_mod_cast (by have := hscale_ge k.val hkd; omega : 0 < scale k.val)
          have hlogSk : (1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1))) * Real.log (scale k.val : ℝ) ≤
              Real.log ((S_cur k).card : ℝ) := by
            have h1 := Real.log_le_log (Real.rpow_pos_of_pos hsk_pos _) (hS_lb k (by omega))
            rwa [Real.log_rpow hsk_pos] at h1
          have h1m_nn : 0 ≤ 1 - 1 / (2 * sqL) := by
            have : 1 / (2 * sqL) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
            linarith
          have hk1_le : (k.val : ℝ) + 1 ≤ sqL / 2 := by
            have : (k.val : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hkd
            linarith
          have hinv_le : 1 / (2 * sqL) ≤ 1 / (4 * ((k.val : ℝ) + 1)) := by
            rw [div_le_div_iff₀ (by linarith) (by positivity)]
            linarith
          have hlog2_le : Real.log 2 ≤ 1 / (4 * ((k.val : ℝ) + 1)) * Real.log (scale k.val : ℝ) := by
            have h1 : 4 * sqL ≤ Real.log (scale k.val : ℝ) := by
              have := hscale_log_lb k.val hkd; linarith
            have h2 : 4 * ((k.val : ℝ) + 1) ≤ Real.log (scale k.val : ℝ) := by linarith
            have h3 : 1 ≤ 1 / (4 * ((k.val : ℝ) + 1)) * Real.log (scale k.val : ℝ) := by
              rw [one_div_mul_eq_div, one_le_div (by positivity)]
              exact h2
            have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
            linarith
          have hprod : 1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1)) - 1 / (4 * ((k.val : ℝ) + 1)) ≤
              (1 - 1 / (2 * sqL)) * (1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1))) := by
            have h1 : (1 - 1 / (2 * sqL)) * (1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1))) =
                1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1)) - 1 / (2 * sqL) +
                  (1 / (2 * sqL)) * ((j : ℝ) / (2 * ((k.val : ℝ) + 1))) := by ring
            have h2 : 0 ≤ (1 / (2 * sqL)) * ((j : ℝ) / (2 * ((k.val : ℝ) + 1))) := by positivity
            linarith
          have hlog_sk_pos : 0 < Real.log (scale k.val : ℝ) := by
            have := hscale_log_lb k.val hkd; linarith
          have hstep : (1 - 1 / (2 * sqL)) * ((1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1))) * Real.log (scale k.val : ℝ)) ≤
              (1 - 1 / (2 * sqL)) * Real.log ((S_cur k).card : ℝ) :=
            mul_le_mul_of_nonneg_left hlogSk h1m_nn
          have hstep2 : (1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1)) - 1 / (4 * ((k.val : ℝ) + 1))) * Real.log (scale k.val : ℝ) ≤
              (1 - 1 / (2 * sqL)) * (1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1))) * Real.log (scale k.val : ℝ) :=
            mul_le_mul_of_nonneg_right hprod hlog_sk_pos.le
          have hstep12 : (1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1)) - 1 / (4 * ((k.val : ℝ) + 1))) * Real.log (scale k.val : ℝ) ≤
              (1 - 1 / (2 * sqL)) * Real.log ((S_cur k).card : ℝ) := by
            rw [mul_assoc] at hstep2
            exact le_trans hstep2 hstep
          have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
          rw [hlog_half]
          have h14 : 1 / (4 * ((k.val : ℝ) + 1)) + 1 / (4 * ((k.val : ℝ) + 1)) =
              1 / (2 * ((k.val : ℝ) + 1)) := by
            have h4 : (4 : ℝ) * ((k.val : ℝ) + 1) = 2 * (2 * ((k.val : ℝ) + 1)) := by ring
            rw [h4, ← add_div, one_add_one_eq_two, div_mul_eq_div_div, div_self (by norm_num : (2 : ℝ) ≠ 0)]
          have hfrac_add : (1 - ((j : ℝ) + 1) / (2 * ((k.val : ℝ) + 1))) * Real.log (scale k.val : ℝ) =
              (1 - (j : ℝ) / (2 * ((k.val : ℝ) + 1)) - 1 / (4 * ((k.val : ℝ) + 1))) * Real.log (scale k.val : ℝ) -
              1 / (4 * ((k.val : ℝ) + 1)) * Real.log (scale k.val : ℝ) := by
            rw [add_div, ← h14]
            ring
          linarith [hfrac_add, hstep12, hlog2_le]
        have hexp_le := Real.exp_le_exp.mpr hlog_target
        have hsk_pos : (0 : ℝ) < (scale k.val : ℝ) := by
          exact_mod_cast (by have := hscale_ge k.val hkd; omega : 0 < scale k.val)
        have hLHS : (scale k.val : ℝ) ^ (1 - ((j : ℝ) + 1) / (2 * ((k.val : ℝ) + 1))) =
            Real.exp ((1 - ((j : ℝ) + 1) / (2 * ((k.val : ℝ) + 1))) * Real.log (scale k.val : ℝ)) := by
          rw [Real.rpow_def_of_pos hsk_pos, mul_comm]
        have hRHS : Real.exp (Real.log ((1 / 2 : ℝ) * ((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL)))) =
            (1 / 2 : ℝ) * ((S_cur k).card : ℝ) ^ (1 - 1 / (2 * sqL)) :=
          Real.exp_log (mul_pos (by norm_num) (Real.rpow_pos_of_pos hSk_pos (1 - 1 / (2 * sqL))))
        linarith [hLHS, hRHS, hexp_le, hm_half]
      -- Update χ at k
      let χ' : Fin d → Bool := fun i => if i = k then c_k else χ i
      refine ⟨T', χ', hT'T.trans hTS, ?_, ?_⟩
      · have hpow_succ : ((1 / 2 : ℝ) ^ (t + 1)) ^ (r + 1) * ((S_cur ⟨j, hj⟩).card : ℝ) =
            ((1 / 2 : ℝ) ^ t / 2) * (((1 / 2 : ℝ) ^ (t + 1)) ^ r * ((S_cur ⟨j, hj⟩).card : ℝ)) := by
          rw [pow_succ, pow_succ]
          ring
        rw [hpow_succ]
        have h1 : (1 / 2 : ℝ) ^ t * (T.card : ℝ) / 2 = ((1 / 2 : ℝ) ^ t / 2) * (T.card : ℝ) := by ring
        rw [h1] at hT'card
        exact le_trans (mul_le_mul_of_nonneg_left hTcard
          (div_nonneg (pow_nonneg (by norm_num) t) (by norm_num))) hT'card
      · intro i hji hi A hAT' hAs
        by_cases hik : i = k
        · subst hik
          simp only [χ', ↓reduceIte]
          exact le_trans hm_lb (Nat.cast_le.mpr (hT'prop A hAT' hAs))
        · simp only [χ', if_neg hik]
          have hile : i.val ≤ j + r := by
            have hne : i.val ≠ j + r + 1 := fun h => hik (Fin.ext h)
            omega
          exact hTprop i hji hile A (hAT'.trans hT'T) hAs
  -- Apply hrec at r = d - 1 - j
  have hlast : j + (d - 1 - j) < d := by omega
  obtain ⟨T, χ, hTS, hTcard, hTprop⟩ := hrec (d - 1 - j) hlast
  -- Verify |T| ≥ (scale j)^(1/4)
  have hSj_lb : (scale j : ℝ) ^ (1 / 2 : ℝ) ≤ ((S_cur ⟨j, hj⟩).card : ℝ) := by
    have h1 := hS_lb ⟨j, hj⟩ le_rfl
    have hexp : (1 / 2 : ℝ) ≤ 1 - (j : ℝ) / (2 * ((j : ℝ) + 1)) := by
      have : (j : ℝ) / (2 * ((j : ℝ) + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    exact le_trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by have := hscale_ge j hj; omega : 1 ≤ scale j)) hexp) h1
  have hT_quarter : (scale j : ℝ) ^ (1 / 4 : ℝ) ≤ (T.card : ℝ) := by
    set r := d - 1 - j
    have hr_le_d : (r : ℝ) ≤ d := by exact_mod_cast (by omega : r ≤ d)
    have ht_ub : (t : ℝ) ≤ Real.log (scale j : ℝ) / (4 * sqL) + 1 :=
      (Nat.ceil_lt_add_one (div_nonneg hlog_sj_pos.le (by linarith))).le
    have hlog2_lt : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have hshrink : (scale j : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ((1 / 2 : ℝ) ^ (t + 1)) ^ r := by
      rw [← pow_mul]
      have hpos2 : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
      rw [show (1 / 2 : ℝ) ^ ((t + 1) * r) = Real.exp (-(((t + 1) * r : ℕ) : ℝ) * Real.log 2) by
        rw [← Real.exp_log hpos2, ← Real.exp_nat_mul]
        congr 1; rw [one_div, Real.log_inv]; ring]
      rw [Real.rpow_def_of_pos (by exact_mod_cast (by have := hscale_ge j hj; omega : 0 < scale j))]
      apply Real.exp_le_exp.mpr
      have h1 : (((t + 1) * r : ℕ) : ℝ) = ((t : ℝ) + 1) * (r : ℝ) := by push_cast; ring
      rw [h1]
      have h2 : ((t : ℝ) + 1) * (r : ℝ) ≤ (Real.log (scale j : ℝ) / (4 * sqL) + 2) * (sqL / 2) :=
        mul_le_mul (by linarith) (le_trans hr_le_d hd_le) (Nat.cast_nonneg r) (by positivity)
      have h3 : (Real.log (scale j : ℝ) / (4 * sqL) + 2) * (sqL / 2) =
          Real.log (scale j : ℝ) / 8 + sqL := by
        have : sqL ≠ 0 := by linarith
        field_simp; ring
      have h4 : sqL ≤ Real.log (scale j : ℝ) / 100 := by
        have := hscale_log_lb j hj; linarith
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h5 : ((t : ℝ) + 1) * (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log (scale j : ℝ) := by linarith
      nlinarith
    have hmul := mul_le_mul hshrink hSj_lb (by positivity) (by positivity)
    have hcomb : (scale j : ℝ) ^ (-(1 / 4 : ℝ)) * (scale j : ℝ) ^ (1 / 2 : ℝ) =
        (scale j : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add (by exact_mod_cast (by have := hscale_ge j hj; omega : 0 < scale j))]
      norm_num
    linarith
  refine ⟨T, χ, hTS, hT_quarter, fun k hjk A hAT hAs => ?_⟩
  exact hTprop k hjk (by omega) A hAT hAs

private lemma exists_max_clique_and_indep {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (hT : T.Nonempty) :
    ∃ (R B : Finset V), R ⊆ T ∧ B ⊆ T ∧
      G.IsClique (R : Set V) ∧ G.IsIndepSet (B : Set V) ∧
      R.Nonempty ∧ B.Nonempty ∧
      (∀ K ⊆ T, G.IsClique (K : Set V) → K.card ≤ R.card) ∧
      (∀ L ⊆ T, G.IsIndepSet (L : Set V) → L.card ≤ B.card) := by
  classical
  let cl : Finset (Finset V) := T.powerset.filter (fun K => G.IsClique (K : Set V))
  let ind : Finset (Finset V) := T.powerset.filter (fun L => G.IsIndepSet (L : Set V))
  obtain ⟨v, hv⟩ := hT
  have hcl_ne : cl.Nonempty := ⟨{v}, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hv), by simp⟩⟩
  have hind_ne : ind.Nonempty := ⟨{v}, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hv), by simp⟩⟩
  obtain ⟨R, hRmem, hRmax⟩ := Finset.exists_max_image cl Finset.card hcl_ne
  obtain ⟨B, hBmem, hBmax⟩ := Finset.exists_max_image ind Finset.card hind_ne
  have hRT : R ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hRmem).1
  have hBT : B ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hBmem).1
  have hRcl : G.IsClique (R : Set V) := (Finset.mem_filter.mp hRmem).2
  have hBind : G.IsIndepSet (B : Set V) := (Finset.mem_filter.mp hBmem).2
  have hRne : R.Nonempty := Finset.card_pos.mp (by
    have := hRmax {v} (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hv), by simp⟩)
    simpa using this)
  have hBne : B.Nonempty := Finset.card_pos.mp (by
    have := hBmax {v} (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hv), by simp⟩)
    simpa using this)
  refine ⟨R, B, hRT, hBT, hRcl, hBind, hRne, hBne, ?_, ?_⟩
  · intro K hKT hKcl
    exact hRmax K (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hKT, hKcl⟩)
  · intro L hLT hLind
    exact hBmax L (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hLT, hLind⟩)

set_option maxHeartbeats 1200000 in
private lemma erdos_191_conlon_fox_sudakov_of_large (n : ℕ)
    (hL : 10000 ≤ Real.log (Real.log (n : ℝ)))
    (G : SimpleGraph (Finset.Icc 2 n)) :
    ∃ X : Finset (Finset.Icc 2 n),
      (G.IsClique (X : Set (Finset.Icc 2 n)) ∨ G.IsIndepSet (X : Set (Finset.Icc 2 n))) ∧
      (2 : ℝ) ^ (-8 : ℤ) * Real.log (Real.log (Real.log (n : ℝ))) ≤
        ∑ x ∈ X, 1 / Real.log ((x : ℕ) : ℝ) := by
  classical
  set L : ℝ := Real.log (Real.log (n : ℝ))
  set sqL : ℝ := Real.sqrt L
  have hsqL : 100 ≤ sqL := by
    have : Real.sqrt 10000 ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
    have h100 : Real.sqrt 10000 = 100 := by
      rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hsqL_sq : sqL ^ 2 = L := Real.sq_sqrt (by linarith)
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by linarith)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by
    by_contra hle; push Not at hle
    have : Real.log (Real.log (n : ℝ)) ≤ 0 := by
      by_cases h0 : Real.log (n : ℝ) = 0
      · simp [h0]
      · have hneg : Real.log (n : ℝ) < 0 := lt_of_le_of_ne hle h0
        have : Real.log (Real.log (n : ℝ)) = Real.log (-(Real.log (n : ℝ))) := by
          rw [← Real.log_abs, abs_of_neg hneg]
        -- Even simpler: if n ≤ 1 then log n = 0, so L = 0 < 10000
        have hn1 : n ≤ 1 := by
          by_contra hgt; push Not at hgt
          have : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
          linarith
        have : Real.log (n : ℝ) = 0 := by
          interval_cases n <;> simp
        linarith
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    by_contra hle; push Not at hle
    have hn0 : n = 0 := by
      have : (n : ℝ) ≤ 0 := hle
      exact_mod_cast Nat.eq_zero_of_le_zero (by exact_mod_cast this)
    subst hn0; simp [L] at hL; linarith
  have hlogn_eq : Real.log (n : ℝ) = Real.exp L := (Real.exp_log hlogn_pos).symm
  let d : ℕ := Nat.floor (sqL / 2) - 1
  have hd_ge : 49 ≤ d := by
    have : 50 ≤ Nat.floor (sqL / 2) := Nat.le_floor (by linarith)
    omega
  have hd_pos : 0 < d := by omega
  have hd_le_half : (d : ℝ) + 1 ≤ sqL / 2 := by
    have hfl : (Nat.floor (sqL / 2) : ℝ) ≤ sqL / 2 := Nat.floor_le (by linarith)
    have h1 : 1 ≤ Nat.floor (sqL / 2) := Nat.le_floor (by linarith)
    have : (d : ℝ) + 1 = (Nat.floor (sqL / 2) : ℝ) := by
      simp only [d]; rw [Nat.cast_sub h1]; push_cast; ring
    linarith
  have hd_le : (d : ℝ) ≤ sqL / 2 := by linarith
  have hd_ge_third : sqL / 3 ≤ (d : ℝ) := by
    have hfl : sqL / 2 - 1 < (Nat.floor (sqL / 2) : ℝ) := Nat.sub_one_lt_floor (sqL / 2)
    have h1 : 1 ≤ Nat.floor (sqL / 2) := Nat.le_floor (by linarith)
    have : (d : ℝ) = (Nat.floor (sqL / 2) : ℝ) - 1 := by
      simp only [d]; rw [Nat.cast_sub h1]; push_cast; ring
    linarith
  have hlogd_lb : (1 / 3 : ℝ) * Real.log L ≤ Real.log (d : ℝ) := by
    have h1 : Real.log (sqL / 3) ≤ Real.log (d : ℝ) := Real.log_le_log (by linarith) hd_ge_third
    rw [Real.log_div (by linarith) (by norm_num), Real.log_sqrt (by linarith)] at h1
    have hlog3 : 6 * Real.log 3 ≤ Real.log L := by
      have : (3 : ℝ) ^ 6 ≤ L := by norm_num; linarith
      have := Real.log_le_log (by norm_num) this
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    linarith
  -- Define scales
  let E : ℕ → ℝ := fun i => ((i : ℝ) + 1) * sqL + L / 2
  let scale : ℕ → ℕ := fun i => Nat.floor (Real.exp (Real.exp (E i)))
  have hE_lb : ∀ i : ℕ, 5000 ≤ E i := by
    intro i; simp only [E]; nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hexpE_lb : ∀ i : ℕ, 1000 * sqL ≤ Real.exp (E i) := by
    intro i
    have h1 := exp_ge_pow_six_div (E i) (by linarith [hE_lb i])
    have h2 : sqL ≤ E i := by simp only [E]; nlinarith [Nat.cast_nonneg (α := ℝ) i]
    have h3 : 5000 ≤ E i := hE_lb i
    have h4 : 1000 * (E i) ≤ (E i) ^ 6 / 720 := by
      have : (E i) ^ 5 ≥ 5000 ^ 5 := pow_le_pow_left₀ (by norm_num) h3 5
      nlinarith
    linarith
  have hscale_ge : ∀ i < d, 100 ≤ scale i := by
    intro i _
    apply Nat.le_floor
    have h1 : 1000 * sqL ≤ Real.exp (E i) := hexpE_lb i
    have h2 : 100 ≤ Real.exp (E i) := by linarith
    have h3 : Real.exp (E i) + 1 ≤ Real.exp (Real.exp (E i)) := by
      linarith [Real.add_one_le_exp (Real.exp (E i))]
    push_cast
    linarith
  have hscale_log_bounds : ∀ i < d,
      (9 / 10 : ℝ) * Real.exp (E i) ≤ Real.log (scale i : ℝ) ∧
      Real.log (scale i : ℝ) ≤ Real.exp (E i) := by
    intro i hi
    have hsc_pos : (0 : ℝ) < scale i := by
      exact_mod_cast (by have := hscale_ge i hi; omega : 0 < scale i)
    have hsc_le : (scale i : ℝ) ≤ Real.exp (Real.exp (E i)) := Nat.floor_le (Real.exp_pos _).le
    have hsc_gt : Real.exp (Real.exp (E i)) - 1 < (scale i : ℝ) := Nat.sub_one_lt_floor _
    have hhalf : (1 / 2 : ℝ) * Real.exp (Real.exp (E i)) ≤ (scale i : ℝ) := by
      have : (2 : ℝ) ≤ Real.exp (Real.exp (E i)) := by
        have := hscale_ge i hi
        have : (100 : ℝ) ≤ scale i := by exact_mod_cast this
        linarith
      linarith
    constructor
    · have hlog1 := Real.log_le_log (by positivity) hhalf
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hlog1
      have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
      rw [hlog_half] at hlog1
      have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
      have := hexpE_lb i
      linarith
    · have hlog2 := Real.log_le_log hsc_pos hsc_le
      rwa [Real.log_exp] at hlog2
  have hscale_log_lb : ∀ i < d, 100 * sqL ≤ Real.log (scale i : ℝ) := by
    intro i hi
    have h1 := (hscale_log_bounds i hi).1
    have h2 := hexpE_lb i
    linarith
  have hscale_ratio : ∀ j k, j < k → k < d →
      (1 / 2 : ℝ) * Real.exp sqL * Real.log (scale j : ℝ) ≤ Real.log (scale k : ℝ) := by
    intro j k hjk hkd
    have hj_ub := (hscale_log_bounds j (lt_trans hjk hkd)).2
    have hk_lb := (hscale_log_bounds k hkd).1
    have hE_diff : E j + sqL ≤ E k := by
      simp only [E]
      have : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
      nlinarith
    have hexp_mul : Real.exp sqL * Real.exp (E j) ≤ Real.exp (E k) := by
      rw [← Real.exp_add, add_comm]
      exact Real.exp_le_exp.mpr hE_diff
    nlinarith [Real.exp_pos sqL, Real.exp_pos (E j)]
  have hscale_upper : ∀ i < d, 2 * scale i ≤ n := by
    intro i hi
    have hi_le : (i : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hi
    have hE_ub : E i ≤ L - sqL := by
      simp only [E]
      nlinarith
    have hexpE_ub : Real.exp (E i) ≤ Real.log (n : ℝ) / 2 := by
      rw [hlogn_eq]
      calc Real.exp (E i) ≤ Real.exp (L - sqL) := Real.exp_le_exp.mpr hE_ub
        _ = Real.exp L * Real.exp (-sqL) := by rw [sub_eq_add_neg, Real.exp_add]
        _ ≤ Real.exp L * (1 / 2) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos L).le
            rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos sqL) (by norm_num)]
            linarith [Real.add_one_le_exp sqL]
        _ = Real.exp L / 2 := by ring
    have h2sc : (2 : ℝ) * (scale i : ℝ) ≤ (n : ℝ) := by
      have hsc_le : (scale i : ℝ) ≤ Real.exp (Real.exp (E i)) := Nat.floor_le (Real.exp_pos _).le
      have hlog2_le : Real.log 2 ≤ Real.log (n : ℝ) / 2 := by
        have h1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
        have h2 : (10000 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
        rw [hlogn_eq]; linarith
      calc (2 : ℝ) * (scale i : ℝ)
          ≤ Real.exp (Real.log 2) * Real.exp (Real.exp (E i)) := by
              rw [Real.exp_log (by norm_num)]; linarith
        _ = Real.exp (Real.log 2 + Real.exp (E i)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
        _ = (n : ℝ) := Real.exp_log hn_pos
    exact_mod_cast h2sc
  have hscale_disj : ∀ i j, i < j → j < d → 2 * scale i ≤ scale j := by
    intro i j hij hjd
    have hrat := hscale_ratio i j hij hjd
    have hlog_si : 100 * sqL ≤ Real.log (scale i : ℝ) := hscale_log_lb i (lt_trans hij hjd)
    have hlog_le : Real.log (2 * (scale i : ℝ)) ≤ Real.log (scale j : ℝ) := by
      rw [Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr (by have := hscale_ge i (lt_trans hij hjd); omega))]
      have hexp_ge : 10 ≤ Real.exp sqL := by linarith [Real.add_one_le_exp sqL]
      have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
      nlinarith
    have hle : (2 : ℝ) * (scale i : ℝ) ≤ (scale j : ℝ) := by
      by_contra hlt; push Not at hlt
      have := Real.log_lt_log (by exact_mod_cast (by have := hscale_ge j hjd; omega : 0 < scale j)) hlt
      linarith
    exact_mod_cast hle
  -- Define initial intervals S₀ i ⊆ Finset.Icc 2 n
  let S₀ : Fin d → Finset (Finset.Icc 2 n) := fun i =>
    Finset.univ.filter (fun x : Finset.Icc 2 n => scale i.val ≤ x.val ∧ x.val < 2 * scale i.val)
  have hS₀_card : ∀ i : Fin d, (S₀ i).card = scale i.val := by
    intro i
    have hbij : (S₀ i).card = (Finset.Ico (scale i.val) (2 * scale i.val)).card := by
      refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
      · intro x hx
        have hf := (Finset.mem_filter.mp hx).2
        exact Finset.mem_Ico.mpr hf
      · intro x _ y _ hxy
        exact Subtype.ext hxy
      · intro m hm
        have hm' := Finset.mem_Ico.mp hm
        have hm_mem : m ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr
          ⟨by have := hscale_ge i.val i.isLt; omega, by have := hscale_upper i.val i.isLt; omega⟩
        exact ⟨⟨m, hm_mem⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'⟩, rfl⟩
    rw [hbij, Nat.card_Ico]
    omega
  have hS₀_disj : ∀ i j : Fin d, i ≠ j → Disjoint (S₀ i) (S₀ j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hi := (Finset.mem_filter.mp hxi).2
    have hj := (Finset.mem_filter.mp hxj).2
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · have := hscale_disj i.val j.val hlt j.isLt; omega
    · have := hscale_disj j.val i.val hlt i.isLt; omega
  -- Helper: weight of a subset of S₀ i
  have hweight_sub : ∀ (i : Fin d) (A : Finset (Finset.Icc 2 n)), A ⊆ S₀ i →
      (A.card : ℝ) / (2 * Real.log (scale i.val : ℝ)) ≤
        ∑ x ∈ A, 1 / Real.log ((x : ℕ) : ℝ) := by
    intro i A hA
    have hlog_si_pos : 0 < Real.log (scale i.val : ℝ) := by
      have := hscale_log_lb i.val i.isLt; linarith
    calc (A.card : ℝ) / (2 * Real.log (scale i.val : ℝ))
        = ∑ _x ∈ A, 1 / (2 * Real.log (scale i.val : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ ∑ x ∈ A, 1 / Real.log ((x : ℕ) : ℝ) := by
            refine Finset.sum_le_sum fun x hx => ?_
            have hx_mem := (Finset.mem_filter.mp (hA hx)).2
            have hx_ge2 : (2 : ℝ) ≤ (x.val : ℝ) := by
              exact_mod_cast (Finset.mem_Icc.mp x.property).1
            have hlogx_pos : 0 < Real.log (x.val : ℝ) := Real.log_pos (by linarith)
            have hlogx_le : Real.log (x.val : ℝ) ≤ 2 * Real.log (scale i.val : ℝ) := by
              have h1 : (x.val : ℝ) ≤ 2 * (scale i.val : ℝ) := by exact_mod_cast hx_mem.2.le
              have h2 := Real.log_le_log (by linarith) h1
              rw [Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr (by have := hscale_ge i.val i.isLt; omega))] at h2
              have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
              have := hscale_log_lb i.val i.isLt
              linarith
            exact one_div_le_one_div_of_le hlogx_pos hlogx_le
  -- Outer induction over m = 0, ..., d
  have houter : ∀ m : ℕ, m ≤ d →
      (∃ X : Finset (Finset.Icc 2 n),
        (G.IsClique (X : Set (Finset.Icc 2 n)) ∨ G.IsIndepSet (X : Set (Finset.Icc 2 n))) ∧
        (2 : ℝ) ^ (-8 : ℤ) * Real.log L ≤ ∑ x ∈ X, 1 / Real.log ((x : ℕ) : ℝ)) ∨
      ∃ (R B : Fin d → Finset (Finset.Icc 2 n))
        (S_cur : Fin d → Finset (Finset.Icc 2 n))
        (χ : Fin d → Fin d → Bool),
        (∀ i : Fin d, S_cur i ⊆ S₀ i) ∧
        (∀ i : Fin d, m ≤ i.val →
          (scale i.val : ℝ) ^ (1 - (m : ℝ) / (2 * ((i.val : ℝ) + 1))) ≤ ((S_cur i).card : ℝ)) ∧
        (∀ i : Fin d, i.val < m →
          R i ⊆ S₀ i ∧ B i ⊆ S₀ i ∧
          G.IsClique (R i : Set (Finset.Icc 2 n)) ∧
          G.IsIndepSet (B i : Set (Finset.Icc 2 n)) ∧
          (R i).Nonempty ∧ (B i).Nonempty ∧
          let ri := 4 * ((R i).card : ℝ) / Real.log (scale i.val : ℝ)
          let bi := 4 * ((B i).card : ℝ) / Real.log (scale i.val : ℝ)
          (ri ≤ bi → (1 / 4 : ℝ) * Real.log (1 / ri) ≤ bi) ∧
          (bi ≤ ri → (1 / 4 : ℝ) * Real.log (1 / bi) ≤ ri)) ∧
        (∀ a b : Fin d, a.val < b.val → b.val < m →
          ∀ u ∈ R a ∪ B a, ∀ v ∈ R b ∪ B b,
            if χ a b then G.Adj u v else ¬ G.Adj u v) ∧
        (∀ a i : Fin d, a.val < m → m ≤ i.val →
          ∀ u ∈ R a ∪ B a, ∀ v ∈ S_cur i,
            if χ a i then G.Adj u v else ¬ G.Adj u v) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine Or.inr ⟨fun _ => ∅, fun _ => ∅, S₀, fun _ _ => true,
        fun _ => Finset.Subset.refl _, ?_, fun _ h => by omega,
        fun _ _ _ h => by omega, fun _ _ h => by omega⟩
      intro i _
      simp [hS₀_card i]
    | succ m ih =>
      intro hm_le
      rcases ih (by omega) with hdone | ⟨R, B, S_cur, χ, hSsub, hSlb, hRBprop, hcross_done, hcross_rem⟩
      · exact Or.inl hdone
      have hmd : m < d := by omega
      let jm : Fin d := ⟨m, hmd⟩
      -- Apply inner DRC induction at j = m
      have hSm_le : (S_cur jm).card ≤ scale m := by
        calc (S_cur jm).card ≤ (S₀ jm).card := Finset.card_le_card (hSsub jm)
          _ = scale m := hS₀_card jm
      obtain ⟨T, χ_m, hTsub, hTcard, hTprop⟩ :=
        inner_drc_induction G d L hL scale hscale_ge hscale_log_lb hscale_ratio hd_le
          m hmd S_cur hSm_le hSlb
      have hT_ge2 : 2 ≤ T.card := by
        have h1 : (2 : ℝ) ≤ (scale m : ℝ) ^ (1 / 4 : ℝ) := by
          have h100 : (16 : ℝ) ≤ (scale m : ℝ) := by
            exact_mod_cast (by have := hscale_ge m hmd; omega : 16 ≤ scale m)
          have := Real.rpow_le_rpow (by norm_num) h100 (by norm_num : (0 : ℝ) ≤ 1 / 4)
          have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
            rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
          linarith
        exact_mod_cast le_trans h1 hTcard
      have hT_ne : T.Nonempty := Finset.card_pos.mp (by omega)
      -- Take maximum red clique Rm and maximum blue clique Bm in T
      obtain ⟨Rm, Bm, hRmT, hBmT, hRm_cl, hBm_ind, hRm_ne, hBm_ne, hRm_max, hBm_max⟩ :=
        exists_max_clique_and_indep G T hT_ne
      have hlog_sm_pos : 0 < Real.log (scale m : ℝ) := by
        have := hscale_log_lb m hmd; linarith
      let rm : ℝ := 4 * (Rm.card : ℝ) / Real.log (scale m : ℝ)
      let bm : ℝ := 4 * (Bm.card : ℝ) / Real.log (scale m : ℝ)
      -- Early exit if rm ≥ log L / 2 or bm ≥ log L / 2
      by_cases hbig : Real.log L / 2 ≤ rm ∨ Real.log L / 2 ≤ bm
      · refine Or.inl ?_
        rcases hbig with hrbig | hbbig
        · refine ⟨Rm, Or.inl hRm_cl, ?_⟩
          have hw := hweight_sub jm Rm (hRmT.trans (hTsub.trans (hSsub jm)))
          have h1 : (Rm.card : ℝ) / (2 * Real.log (scale m : ℝ)) = rm / 8 := by
            change (Rm.card : ℝ) / (2 * Real.log (scale m : ℝ)) = (4 * (Rm.card : ℝ) / Real.log (scale m : ℝ)) / 8
            ring
          rw [h1] at hw
          have hpow8 : (2 : ℝ) ^ (-8 : ℤ) = 1 / 256 := by norm_num
          rw [hpow8]; linarith
        · refine ⟨Bm, Or.inr hBm_ind, ?_⟩
          have hw := hweight_sub jm Bm (hBmT.trans (hTsub.trans (hSsub jm)))
          have h1 : (Bm.card : ℝ) / (2 * Real.log (scale m : ℝ)) = bm / 8 := by
            change (Bm.card : ℝ) / (2 * Real.log (scale m : ℝ)) = (4 * (Bm.card : ℝ) / Real.log (scale m : ℝ)) / 8
            ring
          rw [h1] at hw
          have hpow8 : (2 : ℝ) ^ (-8 : ℤ) = 1 / 256 := by norm_num
          rw [hpow8]; linarith
      push Not at hbig
      -- Verify the weighted Ramsey balance condition for (rm, bm)
      have hlogT_lb : (1 / 4 : ℝ) * Real.log (scale m : ℝ) ≤ Real.log (T.card : ℝ) := by
        have hsm_pos : (0 : ℝ) < (scale m : ℝ) := by
          exact_mod_cast (by have := hscale_ge m hmd; omega : 0 < scale m)
        have h1 := Real.log_le_log (Real.rpow_pos_of_pos hsm_pos _) hTcard
        rwa [Real.log_rpow hsm_pos] at h1
      have hrm_pos : 0 < rm := div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hRm_ne.card_pos)) hlog_sm_pos
      have hbm_pos : 0 < bm := div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hBm_ne.card_pos)) hlog_sm_pos
      have hlog4_lt2 : Real.log 4 < 2 := by
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
        linarith [Real.log_two_lt_d9]
      have hbalance_br : bm ≤ rm → (1 / 4 : ℝ) * Real.log (1 / bm) ≤ rm := by
        intro hle
        by_cases hbm14 : 1 / 4 ≤ bm
        · have hlog_le : (1 / 4 : ℝ) * Real.log (1 / bm) ≤ 1 / 2 := by
            have h1 : 1 / bm ≤ 4 := by rw [div_le_iff₀ hbm_pos]; linarith
            have h2 := Real.log_le_log (div_pos one_pos hbm_pos) h1
            linarith
          have hrm_half : 1 / 2 ≤ rm := by
            rcases ramsey_symm G T hT_ge2 with ⟨K, hKT, hKcl, hKcard⟩ | ⟨Lset, hLT, hLind, hLcard⟩
            · have hleR : (K.card : ℝ) ≤ (Rm.card : ℝ) := Nat.cast_le.mpr (hRm_max K hKT hKcl)
              have : (1 / 8 : ℝ) * Real.log (scale m : ℝ) ≤ (Rm.card : ℝ) := by linarith
              change 1 / 2 ≤ 4 * (Rm.card : ℝ) / Real.log (scale m : ℝ)
              rw [le_div_iff₀ hlog_sm_pos]; linarith
            · have hleB : (Lset.card : ℝ) ≤ (Bm.card : ℝ) := Nat.cast_le.mpr (hBm_max Lset hLT hLind)
              have : (1 / 8 : ℝ) * Real.log (scale m : ℝ) ≤ (Bm.card : ℝ) := by linarith
              have hbm_half : 1 / 2 ≤ bm := by
                change 1 / 2 ≤ 4 * (Bm.card : ℝ) / Real.log (scale m : ℝ)
                rw [le_div_iff₀ hlog_sm_pos]; linarith
              linarith
          linarith
        · push Not at hbm14
          rcases ramsey_asymm Gᶜ T hT_ge2 bm hbm_pos hbm14.le with
            ⟨K, hKT, hKcl, hKcard⟩ | ⟨Lset, hLT, hLind, hLcard⟩
          · -- K is a clique in Gᶜ, hence an independent set in G!
            have hKind : G.IsIndepSet (K : Set (Finset.Icc 2 n)) := by
              intro x hx y hy hxy
              exact (hKcl hx hy hxy).2
            have hKle : (K.card : ℝ) ≤ (Bm.card : ℝ) := Nat.cast_le.mpr (hBm_max K hKT hKind)
            have hBm_eq : (Bm.card : ℝ) = bm * ((1 / 4 : ℝ) * Real.log (scale m : ℝ)) := by
              change (Bm.card : ℝ) = (4 * (Bm.card : ℝ) / Real.log (scale m : ℝ)) * ((1 / 4 : ℝ) * Real.log (scale m : ℝ))
              rw [show (4 * (Bm.card : ℝ) / Real.log (scale m : ℝ)) * ((1 / 4 : ℝ) * Real.log (scale m : ℝ)) =
                (Bm.card : ℝ) * (Real.log (scale m : ℝ) / Real.log (scale m : ℝ)) by ring,
                div_self hlog_sm_pos.ne', mul_one]
            have hBm_le : (Bm.card : ℝ) ≤ bm * Real.log (T.card : ℝ) := by
              rw [hBm_eq]
              exact mul_le_mul_of_nonneg_left hlogT_lb hbm_pos.le
            linarith
          · -- Lset is an independent set in Gᶜ, hence a clique in G!
            have hLcl : G.IsClique (Lset : Set (Finset.Icc 2 n)) := by
              intro x hx y hy hxy
              have hnot := hLind hx hy hxy
              simp only [SimpleGraph.compl_adj, not_and, not_not] at hnot
              exact hnot hxy
            have hLle : (Lset.card : ℝ) ≤ (Rm.card : ℝ) := Nat.cast_le.mpr (hRm_max Lset hLT hLcl)
            have hrm_ge : Real.exp (1 / (4 * bm)) ≤ rm := by
              have h1 : Real.exp (1 / (4 * bm)) * ((1 / 4 : ℝ) * Real.log (scale m : ℝ)) ≤
                  Real.exp (1 / (4 * bm)) * Real.log (T.card : ℝ) :=
                mul_le_mul_of_nonneg_left hlogT_lb (Real.exp_pos _).le
              change Real.exp (1 / (4 * bm)) ≤ 4 * (Rm.card : ℝ) / Real.log (scale m : ℝ)
              rw [le_div_iff₀ hlog_sm_pos]
              linarith
            have hlog_le_exp : (1 / 4 : ℝ) * Real.log (1 / bm) ≤ Real.exp (1 / (4 * bm)) := by
              have h1 : Real.log (1 / bm) ≤ 1 / bm := by
                linarith [Real.log_le_sub_one_of_pos (div_pos one_pos hbm_pos)]
              have h2 : 1 / (4 * bm) ≤ Real.exp (1 / (4 * bm)) := by
                linarith [Real.add_one_le_exp (1 / (4 * bm))]
              have h3 : (1 / 4 : ℝ) * (1 / bm) = 1 / (4 * bm) := by ring
              linarith
            linarith
      have hbalance_rb : rm ≤ bm → (1 / 4 : ℝ) * Real.log (1 / rm) ≤ bm := by
        intro hle
        by_cases hrm14 : 1 / 4 ≤ rm
        · have hlog_le : (1 / 4 : ℝ) * Real.log (1 / rm) ≤ 1 / 2 := by
            have h1 : 1 / rm ≤ 4 := by rw [div_le_iff₀ hrm_pos]; linarith
            have h2 := Real.log_le_log (div_pos one_pos hrm_pos) h1
            linarith
          have hbm_half : 1 / 2 ≤ bm := by
            rcases ramsey_symm G T hT_ge2 with ⟨K, hKT, hKcl, hKcard⟩ | ⟨Lset, hLT, hLind, hLcard⟩
            · have hleR : (K.card : ℝ) ≤ (Rm.card : ℝ) := Nat.cast_le.mpr (hRm_max K hKT hKcl)
              have : (1 / 8 : ℝ) * Real.log (scale m : ℝ) ≤ (Rm.card : ℝ) := by linarith
              have hrm_half : 1 / 2 ≤ rm := by
                change 1 / 2 ≤ 4 * (Rm.card : ℝ) / Real.log (scale m : ℝ)
                rw [le_div_iff₀ hlog_sm_pos]; linarith
              linarith
            · have hleB : (Lset.card : ℝ) ≤ (Bm.card : ℝ) := Nat.cast_le.mpr (hBm_max Lset hLT hLind)
              have : (1 / 8 : ℝ) * Real.log (scale m : ℝ) ≤ (Bm.card : ℝ) := by linarith
              change 1 / 2 ≤ 4 * (Bm.card : ℝ) / Real.log (scale m : ℝ)
              rw [le_div_iff₀ hlog_sm_pos]; linarith
          linarith
        · push Not at hrm14
          rcases ramsey_asymm G T hT_ge2 rm hrm_pos hrm14.le with
            ⟨K, hKT, hKcl, hKcard⟩ | ⟨Lset, hLT, hLind, hLcard⟩
          · have hKle : (K.card : ℝ) ≤ (Rm.card : ℝ) := Nat.cast_le.mpr (hRm_max K hKT hKcl)
            have hRm_eq : (Rm.card : ℝ) = rm * ((1 / 4 : ℝ) * Real.log (scale m : ℝ)) := by
              change (Rm.card : ℝ) = (4 * (Rm.card : ℝ) / Real.log (scale m : ℝ)) * ((1 / 4 : ℝ) * Real.log (scale m : ℝ))
              rw [show (4 * (Rm.card : ℝ) / Real.log (scale m : ℝ)) * ((1 / 4 : ℝ) * Real.log (scale m : ℝ)) =
                (Rm.card : ℝ) * (Real.log (scale m : ℝ) / Real.log (scale m : ℝ)) by ring,
                div_self hlog_sm_pos.ne', mul_one]
            have hRm_le : (Rm.card : ℝ) ≤ rm * Real.log (T.card : ℝ) := by
              rw [hRm_eq]
              exact mul_le_mul_of_nonneg_left hlogT_lb hrm_pos.le
            linarith
          · have hLle : (Lset.card : ℝ) ≤ (Bm.card : ℝ) := Nat.cast_le.mpr (hBm_max Lset hLT hLind)
            have hbm_ge : Real.exp (1 / (4 * rm)) ≤ bm := by
              have h1 : Real.exp (1 / (4 * rm)) * ((1 / 4 : ℝ) * Real.log (scale m : ℝ)) ≤
                  Real.exp (1 / (4 * rm)) * Real.log (T.card : ℝ) :=
                mul_le_mul_of_nonneg_left hlogT_lb (Real.exp_pos _).le
              change Real.exp (1 / (4 * rm)) ≤ 4 * (Bm.card : ℝ) / Real.log (scale m : ℝ)
              rw [le_div_iff₀ hlog_sm_pos]
              linarith
            have hlog_le_exp : (1 / 4 : ℝ) * Real.log (1 / rm) ≤ Real.exp (1 / (4 * rm)) := by
              have h1 : Real.log (1 / rm) ≤ 1 / rm := by
                linarith [Real.log_le_sub_one_of_pos (div_pos one_pos hrm_pos)]
              have h2 : 1 / (4 * rm) ≤ Real.exp (1 / (4 * rm)) := by
                linarith [Real.add_one_le_exp (1 / (4 * rm))]
              have h3 : (1 / 4 : ℝ) * (1 / rm) = 1 / (4 * rm) := by ring
              linarith
            linarith
      -- Pad Rm ∪ Bm to a subset A ⊆ T of size s
      let s_m := Nat.ceil (Real.log (scale m : ℝ) * Real.log L)
      have hRB_le_sm : (Rm ∪ Bm).card ≤ s_m := by
        have h1 : ((Rm ∪ Bm).card : ℝ) ≤ (Rm.card : ℝ) + (Bm.card : ℝ) := by
          exact_mod_cast Finset.card_union_le Rm Bm
        have h2 : (Rm.card : ℝ) = (1 / 4 : ℝ) * rm * Real.log (scale m : ℝ) := by
          change (Rm.card : ℝ) = (1 / 4 : ℝ) * (4 * (Rm.card : ℝ) / Real.log (scale m : ℝ)) * Real.log (scale m : ℝ)
          rw [show (1 / 4 : ℝ) * (4 * (Rm.card : ℝ) / Real.log (scale m : ℝ)) * Real.log (scale m : ℝ) =
            (Rm.card : ℝ) * (Real.log (scale m : ℝ) / Real.log (scale m : ℝ)) by ring,
            div_self hlog_sm_pos.ne', mul_one]
        have h3 : (Bm.card : ℝ) = (1 / 4 : ℝ) * bm * Real.log (scale m : ℝ) := by
          change (Bm.card : ℝ) = (1 / 4 : ℝ) * (4 * (Bm.card : ℝ) / Real.log (scale m : ℝ)) * Real.log (scale m : ℝ)
          rw [show (1 / 4 : ℝ) * (4 * (Bm.card : ℝ) / Real.log (scale m : ℝ)) * Real.log (scale m : ℝ) =
            (Bm.card : ℝ) * (Real.log (scale m : ℝ) / Real.log (scale m : ℝ)) by ring,
            div_self hlog_sm_pos.ne', mul_one]
        have h4 : ((Rm ∪ Bm).card : ℝ) ≤ Real.log (scale m : ℝ) * Real.log L := by
          nlinarith [hbig.1, hbig.2]
        have h5 : ((Rm ∪ Bm).card : ℝ) ≤ (s_m : ℝ) := le_trans h4 (Nat.le_ceil _)
        exact_mod_cast h5
      have hsm_le_T : s_m ≤ T.card := by
        have hs_ub : (s_m : ℝ) ≤ Real.log (scale m : ℝ) * Real.log L + 1 :=
          (Nat.ceil_lt_add_one (mul_nonneg hlog_sm_pos.le hlogL_pos.le)).le
        have hlogL_le : Real.log L ≤ 2 * sqL := log_le_sqrt_mul_two L (by linarith)
        have hlog_sm_le : Real.log (scale m : ℝ) * Real.log L + 1 ≤ (scale m : ℝ) ^ (1 / 4 : ℝ) := by
          set z := Real.log (scale m : ℝ) / 4
          have hz_ge : sqL ≤ z := by
            simp only [z]; have := hscale_log_lb m hmd; linarith
          have hz_pos : 0 < z := by linarith
          have hexp_z : (scale m : ℝ) ^ (1 / 4 : ℝ) = Real.exp z := by
            rw [Real.rpow_def_of_pos (by exact_mod_cast (by have := hscale_ge m hmd; omega : 0 < scale m))]
            congr 1; simp only [z]; ring
          rw [hexp_z]
          have h6 := exp_ge_pow_six_div z hz_pos.le
          have h100z : 100 ≤ z := by linarith
          have hpoly : 8 * z ^ 2 + 1 ≤ z ^ 6 / 720 := by
            have : z ^ 4 ≥ 100 ^ 4 := pow_le_pow_left₀ (by norm_num) h100z 4
            nlinarith [sq_nonneg z]
          have hmul : Real.log (scale m : ℝ) * Real.log L + 1 ≤ 8 * z ^ 2 + 1 := by
            have : Real.log (scale m : ℝ) = 4 * z := by simp only [z]; ring
            nlinarith
          linarith
        exact_mod_cast le_trans (le_trans hs_ub hlog_sm_le) hTcard
      -- Obtain padded set A with Rm ∪ Bm ⊆ A ⊆ T and A.card = s_m
      have hexA : ∃ A : Finset (Finset.Icc 2 n), Rm ∪ Bm ⊆ A ∧ A ⊆ T ∧ A.card = s_m := by
        have hsub : Rm ∪ Bm ⊆ T := Finset.union_subset hRmT hBmT
        have hdiff_le : s_m - (Rm ∪ Bm).card ≤ (T \ (Rm ∪ Bm)).card := by
          have := Finset.card_sdiff_add_card_eq_card hsub; omega
        obtain ⟨P, hPT, hPcard⟩ := Finset.exists_subset_card_eq hdiff_le
        refine ⟨(Rm ∪ Bm) ∪ P, Finset.subset_union_left,
          Finset.union_subset hsub (hPT.trans Finset.sdiff_subset), ?_⟩
        rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hPT disjoint_sdiff_self_right),
          hPcard]
        omega
      obtain ⟨A, hRBA, hAT, hAcard⟩ := hexA
      -- Update R, B, S_cur, χ
      let R' : Fin d → Finset (Finset.Icc 2 n) := fun i => if i = jm then Rm else R i
      let B' : Fin d → Finset (Finset.Icc 2 n) := fun i => if i = jm then Bm else B i
      let χ' : Fin d → Fin d → Bool := fun a i => if a = jm then χ_m i else χ a i
      let S_cur' : Fin d → Finset (Finset.Icc 2 n) := fun i =>
        if m < i.val then
          (S_cur i).filter (fun v => ∀ u ∈ A, if χ_m i then G.Adj u v else ¬ G.Adj u v)
        else S_cur i
      refine Or.inr ⟨R', B', S_cur', χ', ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        by_cases hmi : m < i.val
        · simp only [S_cur', if_pos hmi]
          exact (Finset.filter_subset _ _).trans (hSsub i)
        · simp only [S_cur', if_neg hmi]
          exact hSsub i
      · intro i hi
        have hmi : m < i.val := by omega
        simp only [S_cur', if_pos hmi]
        have h := hTprop i hmi A hAT hAcard
        simpa [Nat.cast_add, Nat.cast_one] using h
      · intro i hi
        by_cases him : i = jm
        · subst him
          simp only [R', B', ↓reduceIte]
          exact ⟨hRmT.trans (hTsub.trans (hSsub jm)), hBmT.trans (hTsub.trans (hSsub jm)),
            hRm_cl, hBm_ind, hRm_ne, hBm_ne, hbalance_rb, hbalance_br⟩
        · simp only [R', B', if_neg him]
          have hlt : i.val < m := by
            have : i.val ≠ m := fun h => him (Fin.ext h)
            omega
          exact hRBprop i hlt
      · intro a b hab hbm u hu v hv
        have ha_ne : a ≠ jm := fun h => by subst h; simp only [jm] at hab; omega
        simp only [R', B', χ', if_neg ha_ne] at hu ⊢
        by_cases hbm_eq : b = jm
        · subst hbm_eq
          simp only [R', B', ↓reduceIte] at hv
          have hv_in_Sm : v ∈ S_cur jm := hTsub (Finset.union_subset hRmT hBmT hv)
          exact hcross_rem a jm (by omega) le_rfl u hu v hv_in_Sm
        · simp only [R', B', if_neg hbm_eq] at hv
          have hb_lt : b.val < m := by
            have : b.val ≠ m := fun h => hbm_eq (Fin.ext h)
            omega
          exact hcross_done a b hab hb_lt u hu v hv
      · intro a i ha hi u hu v hv
        have hmi : m < i.val := by omega
        simp only [S_cur', if_pos hmi, Finset.mem_filter] at hv
        by_cases ham : a = jm
        · subst ham
          simp only [R', B', χ', ↓reduceIte] at hu ⊢
          exact hv.2 u (hRBA hu)
        · simp only [R', B', χ', if_neg ham] at hu ⊢
          have ha_lt : a.val < m := by
            have : a.val ≠ m := fun h => ham (Fin.ext h)
            omega
          exact hcross_rem a i ha_lt (by omega) u hu v hv.1
  -- Finish using houter at m = d
  rcases houter d le_rfl with hdone | ⟨R, B, _, χ, _, _, hRBprop, hcross, _⟩
  · exact hdone
  -- Build reduced graph on Fin d
  let Gred : SimpleGraph (Fin d) :=
    { Adj := fun a b => (a.val < b.val ∧ χ a b = true) ∨ (b.val < a.val ∧ χ b a = true)
      symm := ⟨fun a b h => by
        rcases h with h | h
        · exact Or.inr h
        · exact Or.inl h⟩
      loopless := ⟨fun a h => by
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h⟩ }
  let rw_fn : Fin d → ℝ := fun i => 4 * ((R i).card : ℝ) / Real.log (scale i.val : ℝ)
  let bw_fn : Fin d → ℝ := fun i => 4 * ((B i).card : ℝ) / Real.log (scale i.val : ℝ)
  have hwr := weighted_ramsey Gred (Finset.univ : Finset (Fin d))
    (Finset.card_pos.mp (by simp [hd_pos])) (1 / 4) (by norm_num) rw_fn bw_fn
    (fun i _ => by
      have hp := hRBprop i i.isLt
      have hlog := hscale_log_lb i.val i.isLt
      exact div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hp.2.2.2.2.1.card_pos)) (by linarith))
    (fun i _ => by
      have hp := hRBprop i i.isLt
      have hlog := hscale_log_lb i.val i.isLt
      exact div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hp.2.2.2.2.2.1.card_pos)) (by linarith))
    (fun i _ hle => by
      have hp := hRBprop i i.isLt
      have h4c : 4 * (1 / 4 : ℝ) = 1 := by norm_num
      rw [h4c]
      exact hp.2.2.2.2.2.2.1 hle)
    (fun i _ hle => by
      have hp := hRBprop i i.isLt
      have h4c : 4 * (1 / 4 : ℝ) = 1 := by norm_num
      rw [h4c]
      exact hp.2.2.2.2.2.2.2 hle)
  have hcard_univ : ((Finset.univ : Finset (Fin d)).card : ℝ) = (d : ℝ) := by simp
  rw [hcard_univ] at hwr
  have hpow8 : (2 : ℝ) ^ (-8 : ℤ) = 1 / 256 := by norm_num
  rcases hwr with ⟨K, _, hKcl, hKsum⟩ | ⟨Lset, _, hLind, hLsum⟩
  · -- Red clique X = K.biUnion R
    let X := K.biUnion R
    refine ⟨X, Or.inl ?_, ?_⟩
    · intro u hu v hv huv
      simp only [X, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hu hv
      obtain ⟨a, haK, hua⟩ := hu
      obtain ⟨b, hbK, hvb⟩ := hv
      by_cases hab : a = b
      · subst hab
        exact (hRBprop a a.isLt).2.2.1 hua hvb huv
      · have hadj := hKcl haK hbK hab
        rcases hadj with ⟨hlt, hχ⟩ | ⟨hlt, hχ⟩
        · have h := hcross a b hlt b.isLt u (Finset.mem_union_left _ hua) v (Finset.mem_union_left _ hvb)
          simpa [hχ] using h
        · have h := hcross b a hlt a.isLt v (Finset.mem_union_left _ hvb) u (Finset.mem_union_left _ hua)
          exact (by simpa [hχ] using h : G.Adj v u).symm
    · have hpw : Set.PairwiseDisjoint (K : Set (Fin d)) R := by
        intro a _ b _ hab
        exact Disjoint.mono (hRBprop a a.isLt).1 (hRBprop b b.isLt).1 (hS₀_disj a b hab)
      rw [Finset.sum_biUnion hpw]
      have hsum_ge : ∑ i ∈ K, rw_fn i / 8 ≤ ∑ i ∈ K, ∑ x ∈ R i, 1 / Real.log ((x : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hw := hweight_sub i (R i) (hRBprop i i.isLt).1
        have hlog_pos : 0 < Real.log (scale i.val : ℝ) := by
          have := hscale_log_lb i.val i.isLt; linarith
        have heq : ((R i).card : ℝ) / (2 * Real.log (scale i.val : ℝ)) = rw_fn i / 8 := by
          change ((R i).card : ℝ) / (2 * Real.log (scale i.val : ℝ)) =
            (4 * ((R i).card : ℝ) / Real.log (scale i.val : ℝ)) / 8
          ring
        linarith
      rw [← Finset.sum_div] at hsum_ge
      rw [hpow8]
      linarith
  · -- Blue clique X = Lset.biUnion B
    let X := Lset.biUnion B
    refine ⟨X, Or.inr ?_, ?_⟩
    · intro u hu v hv huv
      simp only [X, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hu hv
      obtain ⟨a, haL, hua⟩ := hu
      obtain ⟨b, hbL, hvb⟩ := hv
      by_cases hab : a = b
      · subst hab
        exact (hRBprop a a.isLt).2.2.2.1 hua hvb huv
      · have hnot := hLind haL hbL hab
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
        · have hχ : χ a b = false := by
            cases hc : χ a b
            · rfl
            · exact absurd (Or.inl ⟨hlt, hc⟩) hnot
          have h := hcross a b hlt b.isLt u (Finset.mem_union_right _ hua) v (Finset.mem_union_right _ hvb)
          simpa [hχ] using h
        · have hχ : χ b a = false := by
            cases hc : χ b a
            · rfl
            · exact absurd (Or.inr ⟨hlt, hc⟩) hnot
          have h := hcross b a hlt a.isLt v (Finset.mem_union_right _ hvb) u (Finset.mem_union_right _ hua)
          exact fun hadj => (by simpa [hχ] using h : ¬ G.Adj v u) hadj.symm
    · have hpw : Set.PairwiseDisjoint (Lset : Set (Fin d)) B := by
        intro a _ b _ hab
        exact Disjoint.mono (hRBprop a a.isLt).2.1 (hRBprop b b.isLt).2.1 (hS₀_disj a b hab)
      rw [Finset.sum_biUnion hpw]
      have hsum_ge : ∑ i ∈ Lset, bw_fn i / 8 ≤ ∑ i ∈ Lset, ∑ x ∈ B i, 1 / Real.log ((x : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hw := hweight_sub i (B i) (hRBprop i i.isLt).2.1
        have hlog_pos : 0 < Real.log (scale i.val : ℝ) := by
          have := hscale_log_lb i.val i.isLt; linarith
        have heq : ((B i).card : ℝ) / (2 * Real.log (scale i.val : ℝ)) = bw_fn i / 8 := by
          change ((B i).card : ℝ) / (2 * Real.log (scale i.val : ℝ)) =
            (4 * ((B i).card : ℝ) / Real.log (scale i.val : ℝ)) / 8
          ring
        linarith
      rw [← Finset.sum_div] at hsum_ge
      rw [hpow8]
      linarith

end Erdos191CFS

theorem OMA.solution : type_of% @Erdos191.erdos_191.variants.conlon_fox_sudakov := by
  have htend : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [htend.eventually_ge_atTop (10000 : ℝ)] with n hn G
  exact Erdos191CFS.erdos_191_conlon_fox_sudakov_of_large n hn G
