import OMAReductions.R_Erdos28_erdos_28_R1

/-!
# A density criterion for the remaining Erdős 28 finite obstruction

TheWaler's reduction in PR 4711 splits the Erdős–Turán conjecture into
a finite obstruction and a finite-edit bound. Claude proved the latter
for @anmolspace in PR 5250. Here the finite obstruction is approached
through a density constraint on hypothetical counterexamples.

The analytic step quantifies how frequently a bounded asymptotic basis
must have six or more ordered representations. The companion proof uses
a finite Fourier estimate; relevant antecedents include Konstantoulas
(Acta Arith. 159, 2013), Sándor (Integers 8, 2008) and Li–Zhang
(Acta Arith. 225, 2026). The remaining finite question only considers
covers maintaining the lower density at every tested scale.

Unrelated finite covers at arbitrarily large cutoffs yield one bounded
infinite basis by compactness. The fixed-prefix argument is in the
tradition of Nathanson, Generalized additive bases, König's lemma, and
the Erdős–Turán conjecture. Formalization for @anmolspace with OpenAI Codex.
-/

namespace OMA.Erdos28DensityTransfer

open Finset Filter AdditiveCombinatorics
open scoped Topology

theorem count_prefix (A B : Set ℕ) (n : ℕ)
    (agree : ∀ x ≤ n, x ∈ A ↔ x ∈ B) : sumRep A n = sumRep B n := by
  classical
  rw [sumRep_def, sumRep_def]
  congr 1
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨hp,ha,hb⟩
    have hsum : p.1+p.2=n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact ⟨hp, (agree _ (by omega)).mp ha, (agree _ (by omega)).mp hb⟩
  · rintro ⟨hp,ha,hb⟩
    have hsum : p.1+p.2=n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact ⟨hp, (agree _ (by omega)).mpr ha, (agree _ (by omega)).mpr hb⟩

/-- Arbitrarily long feasible prefixes at one fixed cap yield one exact
infinite basis at the same cap. The finite prefixes need not be nested. -/
theorem infinite_counterexample (g : ℕ)
    (bad : ¬ ∃ L : ℕ, ∀ S : Finset ℕ, S ⊆ Iic L →
      (∀ n ≤ L, ∃ a ∈ S, ∃ b ∈ S, a+b=n) → ∃ n ≤ L, g < sumRep (S : Set ℕ) n) :
    ∃ A : Set ℕ, (∀ n, ∃ a∈A, ∃ b∈A, a+b=n) ∧ ∀ n, sumRep A n ≤ g := by
  classical
  push Not at bad
  choose S sub cov cap using bad
  let bits (L j : ℕ) : Bool := decide (j ∈ S L)
  obtain ⟨v,φ,hφ,ht⟩ := CompactSpace.tendsto_subseq bits
  let A : Set ℕ := {j | v j = true}
  have pickRow (n : ℕ) : ∃ L ≥ n, ∀ j ≤ n, j ∈ A ↔ j ∈ S L := by
    have one (j : ℕ) : ∀ᶠ k in atTop, bits (φ k) j = v j := by
      have hh := tendsto_pi_nhds.mp ht j
      rw [nhds_discrete Bool] at hh
      exact tendsto_pure.mp hh
    have window : ∀ᶠ k in atTop, ∀ j ∈ Iic n, bits (φ k) j = v j :=
      (eventually_all_finset _).mpr (fun j _ => one j)
    obtain ⟨k,hkn,hw⟩ := ((eventually_ge_atTop n).and window).exists
    refine ⟨φ k,hkn.trans (hφ.id_le k),?_⟩
    intro j hj
    change v j=true ↔ _
    rw [← hw j (mem_Iic.mpr hj)]
    simp [bits]
  refine ⟨A,?_,?_⟩
  · intro n
    obtain ⟨L,hn,ha⟩ := pickRow n
    obtain ⟨a,aa,b,bb,hs⟩ := cov L n hn
    exact ⟨a,(ha _ (by omega)).mpr aa,b,(ha _ (by omega)).mpr bb,hs⟩
  · intro n
    obtain ⟨L,hn,ha⟩ := pickRow n
    rw [count_prefix A (S L : Set ℕ) n ha]
    exact cap L n hn

end OMA.Erdos28DensityTransfer

namespace OMA.R_Erdos28_erdos_28_R1_H1_R2

open AdditiveCombinatorics Finset
open scoped Pointwise

/-- Any eventually bounded asymptotic basis has a fixed positive lower
density of sums with at least six ordered representations. -/
def H1 : Prop := ∀ (A : Set ℕ), (A+A)ᶜ.Finite → ∀ g : ℕ,
    (∃ K, ∀ n≥K, sumRep A n ≤ g) →
    ∃ N₀, ∀ N≥N₀, N ≤ 1024*(g+3)^4*((range N).filter (fun n => 6 ≤ sumRep A n)).card

/-- Only finite covers that maintain the six-representation lower-density
bound at every tested scale need to be ruled out. -/
def H2 : Prop := ∀ g K : ℕ, ∃ L≥K, ∀ S : Finset ℕ, S ⊆ Iic L →
    (∀ n≤L, ∃ a∈S, ∃ b∈S, a+b=n) →
    (∀ N, K≤N → N≤L → N ≤ 1024*(g+3)^4*
      ((range N).filter (fun n => 6 ≤ sumRep (S : Set ℕ) n)).card) →
    ∃ n≤L, g<sumRep (S : Set ℕ) n

theorem main : H1 → H2 → OMA.R_Erdos28_erdos_28_R1.H1 := by
  classical
  intro density finiteTest g
  by_contra fails
  obtain ⟨A,cov,cap⟩ := OMA.Erdos28DensityTransfer.infinite_counterexample g fails
  have full : A+A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro n
    exact cov n
  have cof : (A+A)ᶜ.Finite := by simp [full]
  obtain ⟨K,freq⟩ := density A cof g ⟨0,fun n _ => cap n⟩
  obtain ⟨L,_,test⟩ := finiteTest g K
  let S := (Iic L).filter (·∈A)
  have keep (x) (hx : x≤L) : x∈S ↔ x∈A := by simp [S,hx]
  have eqRep (n) (hn : n≤L) : sumRep (S : Set ℕ) n = sumRep A n :=
    OMA.Erdos28DensityTransfer.count_prefix _ _ n (fun x hx => keep x (hx.trans hn))
  have cover (n) (hn : n≤L) : ∃ a∈S, ∃ b∈S, a+b=n := by
    obtain ⟨a,ha,b,hb,e⟩ := cov n
    exact ⟨a,(keep a (by omega)).mpr ha,b,(keep b (by omega)).mpr hb,e⟩
  have dense (N) (hk : K≤N) (hl : N≤L) : N ≤ 1024*(g+3)^4*
      ((range N).filter (fun n => 6 ≤ sumRep (S : Set ℕ) n)).card := by
    have same : (range N).filter (fun n => 6 ≤ sumRep (S : Set ℕ) n) =
        (range N).filter (fun n => 6 ≤ sumRep A n) := by
      apply Finset.filter_congr
      intro n hn
      rw [eqRep n ((mem_range.mp hn).le.trans hl)]
    rw [same]
    exact freq N hk
  obtain ⟨n,hn,ex⟩ := test S (filter_subset ..) cover dense
  rw [eqRep n hn] at ex
  exact (Nat.not_lt_of_ge (cap n)) ex

end OMA.R_Erdos28_erdos_28_R1_H1_R2
