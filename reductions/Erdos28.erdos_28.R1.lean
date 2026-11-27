import FormalConjectures.ErdosProblems.«28»

/-! Finite obstructions for the Erdős–Turán additive basis conjecture.
The finite-problem approach appears in SIAM J. Discrete Math.,
doi:10.1137/0401016. Finite modifications also appear in the treatment
by Borwein, Choi and Chu. The counts here are ordered. Credit: @TheWaler. -/

open Filter Set AdditiveCombinatorics
open scoped Pointwise

namespace OMA.R_Erdos28_erdos_28_R1

-- For each budget there is a finite interval on which every exact
-- two-sum cover already exceeds that budget at some covered index.
def H1 : Prop :=
  ∀ g : ℕ, ∃ L : ℕ, ∀ S : Finset ℕ, S ⊆ Finset.Iic L →
    (∀ n ≤ L, ∃ a ∈ S, ∃ b ∈ S, a + b = n) →
    ∃ n ≤ L, g < sumRep (S : Set ℕ) n

-- A single inserted element can create at most two ordered pairs per sum.
def H2 : Prop :=
  ∀ (A : Set ℕ) (a n : ℕ), sumRep (insert a A) n ≤ sumRep A n + 2

lemma finite_edit (h : H2) (A : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    sumRep ((F : Set ℕ) ∪ A) n ≤ sumRep A n + 2 * F.card := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    rw [Finset.coe_insert, Set.insert_union, Finset.card_insert_of_notMem ha]
    have := h ((F : Set ℕ) ∪ A) a n
    omega

lemma monotone_count {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    sumRep A n ≤ sumRep B n := by
  classical
  simp only [sumRep_def]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, h hp.2.1, h hp.2.2⟩

theorem main : H1 → H2 → type_of% @Erdos28.erdos_28 := by
  classical
  intro obstruction edit A hA
  let F := insert 0 hA.toFinset
  let B : Set ℕ := (F : Set ℕ) ∪ A
  have cover (n : ℕ) : ∃ a ∈ B, ∃ b ∈ B, a + b = n := by
    by_cases hn : n ∈ A + A
    · obtain ⟨a, ha, b, hb, he⟩ := hn
      exact ⟨a, Or.inr ha, b, Or.inr hb, he⟩
    · exact ⟨0, Or.inl (by simp [F]), n, Or.inl (by simp [F, hn]), Nat.zero_add n⟩
  apply ENat.eq_top_iff_forall_ge.mpr
  intro m
  refine le_limsup_of_frequently_le ?_ ⟨⊤, Filter.Eventually.of_forall (fun _ => le_top)⟩
  rw [frequently_atTop]
  intro k
  let budget := m + (∑ i ∈ Finset.range k, sumRep A i)
  obtain ⟨L, cert⟩ := obstruction (budget + 2 * F.card)
  let S := (Finset.Iic L).filter (· ∈ B)
  have hS : ∀ n ≤ L, ∃ a ∈ S, ∃ b ∈ S, a + b = n := by
    intro n hn
    obtain ⟨a, ha, b, hb, he⟩ := cover n
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (by omega), ha⟩,
      b, Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (by omega), hb⟩, he⟩
  obtain ⟨n, _, hn⟩ := cert S (Finset.filter_subset _ _) hS
  have mono := monotone_count (B := B) (A := (S : Set ℕ))
    (fun i hi => (Finset.mem_filter.mp hi).2) n
  have bound := finite_edit edit A F n
  change sumRep B n ≤ _ at bound
  have big : budget < sumRep A n := by omega
  refine ⟨n, ?_, ?_⟩
  · by_contra! small
    have le := Finset.single_le_sum (f := sumRep A) (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr small)
    dsimp [budget] at big
    omega
  · exact_mod_cast (show m ≤ sumRep A n by dsimp [budget] at big; omega)

end OMA.R_Erdos28_erdos_28_R1
