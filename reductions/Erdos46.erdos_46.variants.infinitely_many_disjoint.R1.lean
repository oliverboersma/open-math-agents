import FormalConjectures.ErdosProblems.«46»

/-!
# Disjoint monochromatic unit fractions

Ernest S. Croot III, On a coloring conjecture about unit fractions, Annals of
Mathematics 157 (2003), 545–556, equation (1.1) and the Main Theorem.
https://annals.math.princeton.edu/wp-content/uploads/annals-v157-n2-p04.pdf

The two inputs ask for large reciprocal mass in a short interval of smooth
integers and for unit-sum extraction from a heavy subset. Both use the same
explicit sublinear error around the normal orders of the two prime-factor counts.
-/

namespace OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1

/-- Arbitrarily far out there are regular pools with reciprocal mass above any prescribed bound. -/
def H1 : Prop :=
  let regular (θ δ : ℝ) (N n : ℕ) :=
    N ≤ n ∧ (n : ℝ) ≤ (N : ℝ) ^ (1 + δ) ∧
    (∀ q ∈ n.divisors, IsPrimePow q → (q : ℝ) ≤ (N : ℝ) ^ θ) ∧
    |(n.primeFactors.card : ℝ) - Real.log (Real.log n)| ≤
      (Real.log (Real.log n)) ^ (3 / 4 : ℝ) ∧
    |(n.primeFactorsList.length : ℝ) - Real.log (Real.log n)| ≤
      (Real.log (Real.log n)) ^ (3 / 4 : ℝ)
  ∃ θ δ : ℝ, 0 < θ ∧ 0 < δ ∧ θ + δ < 1 / 4 ∧
    ∀ r B : ℕ, ∃ N ≥ max 2 B, ∃ P : Finset ℕ,
      (∀ n ∈ P, regular θ δ N n) ∧ 6 * (r : ℚ) < ∑ n ∈ P, (1 / n : ℚ)

/-- Within a regular pool, any set of reciprocal mass greater than six contains a unit sum. -/
def H2 : Prop :=
  let regular (θ δ : ℝ) (N n : ℕ) :=
    N ≤ n ∧ (n : ℝ) ≤ (N : ℝ) ^ (1 + δ) ∧
    (∀ q ∈ n.divisors, IsPrimePow q → (q : ℝ) ≤ (N : ℝ) ^ θ) ∧
    |(n.primeFactors.card : ℝ) - Real.log (Real.log n)| ≤
      (Real.log (Real.log n)) ^ (3 / 4 : ℝ) ∧
    |(n.primeFactorsList.length : ℝ) - Real.log (Real.log n)| ≤
      (Real.log (Real.log n)) ^ (3 / 4 : ℝ)
  ∀ θ δ : ℝ, 0 < θ → 0 < δ → θ + δ < 1 / 4 → ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ C : Finset ℕ, (∀ n ∈ C, regular θ δ N n) →
      6 < (∑ n ∈ C, (1 / n : ℚ)) → ∃ S ⊆ C, (∑ n ∈ S, (1 / n : ℚ)) = 1

/-- Give each denominator at most `B` its own colour. A monochromatic sum of one
cannot use a singleton denominator of size at least two. -/
theorem one_beyond (one : type_of% @Erdos46.erdos_46) (c : ℕ → ℕ)
    (hc : (Set.range c).Finite) (B : ℕ) :
    ∃ S : Finset ℕ, (∀ n ∈ S, B < n) ∧ (∀ n ∈ S, 2 ≤ n) ∧
      ∑ n ∈ S, (1 / n : ℚ) = 1 ∧ (c '' (S : Set ℕ)).Subsingleton := by
  classical
  let f (n : ℕ) := if n ≤ B then n else B + 1 + c n
  have hf : (Set.range f).Finite := by
    apply ((Set.finite_Iic B).union (hc.image (fun j => B + 1 + j))).subset
    rintro _ ⟨n, rfl⟩
    by_cases h : n ≤ B
    · exact Or.inl (by simp [f, h])
    · exact Or.inr ⟨c n, ⟨n, rfl⟩, by simp [f, h]⟩
  obtain ⟨S, hden, hsum, hmono⟩ := one f hf
  have same {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) : f i = f j :=
    hmono ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
  have fresh (i : ℕ) (hi : i ∈ S) : B < i := by
    by_contra! hib
    have singleton : S = {i} := by
      apply Finset.Subset.antisymm
      · intro j hj
        have eq := same hi hj
        by_cases hjb : j ≤ B
        · simpa [f, hib, hjb] using eq.symm
        · simp only [f, if_pos hib, if_neg hjb] at eq
          omega
      · simpa only [Finset.singleton_subset_iff] using hi
    have heq : (1 : ℚ) / i = 1 := by simpa [singleton] using hsum
    have htwo : (2 : ℚ) ≤ i := by exact_mod_cast hden i hi
    have hpos : (0 : ℚ) < i := by linarith
    have := (div_eq_iff hpos.ne').mp heq
    linarith
  refine ⟨S, fresh, hden, hsum, ?_⟩
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  have eq := same hi hj
  simpa [f, (fresh i hi).not_ge, (fresh j hj).not_ge] using eq

/-- Infinitely many pairwise disjoint monochromatic solutions follow from the
existence of one solution for every finite colouring. -/
theorem disjoint_of_one (one : type_of% @Erdos46.erdos_46) :
    type_of% @Erdos46.erdos_46.variants.infinitely_many_disjoint := by
  classical
  intro c hc
  choose S fresh hden hsum hmono using one_beyond one c hc
  let cutoff : ℕ → ℕ := Nat.rec 0 (fun _ b => max b ((S b).sup id))
  have step (i : ℕ) : cutoff (i + 1) = max (cutoff i) ((S (cutoff i)).sup id) := rfl
  have mono : Monotone cutoff := monotone_nat_of_le_succ fun i => by
    rw [step]; exact le_max_left _ _
  have sep {i j : ℕ} (hij : i < j) : Disjoint (S (cutoff i)) (S (cutoff j)) := by
    apply Finset.disjoint_left.mpr
    intro n hi hj
    have hn : n ≤ (S (cutoff i)).sup id := Finset.le_sup (f := id) hi
    have upto : (S (cutoff i)).sup id ≤ cutoff (i + 1) := by
      rw [step]; exact le_max_right _ _
    exact (fresh (cutoff j) n hj).not_ge (hn.trans (upto.trans (mono hij)))
  refine ⟨fun i => S (cutoff i), ?_, fun i => ⟨hden _, hsum _, hmono _⟩⟩
  intro i j hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact sep h
  · exact (sep h).symm

/-- Partition a finite pool by colour and sum its reciprocal weights by fibres. -/
lemma heavy_fibre (P K : Finset ℕ) (c : ℕ → ℕ)
    (maps : ∀ n ∈ P, c n ∈ K) (mass : 6 * (K.card : ℚ) < ∑ n ∈ P, (1 / n : ℚ)) :
    ∃ j ∈ K, 6 < ∑ n ∈ P.filter (fun n => c n = j), (1 / n : ℚ) := by
  by_contra! bound
  have total := Finset.sum_le_sum bound
  rw [Finset.sum_fiberwise_of_maps_to maps] at total
  simp only [Finset.sum_const, nsmul_eq_mul] at total
  linarith

theorem main : H1 → H2 → type_of% @Erdos46.erdos_46.variants.infinitely_many_disjoint := by
  classical
  intro pools extract
  obtain ⟨θ, δ, hθ, hδ, hsum, pool⟩ := pools
  obtain ⟨N₀, get⟩ := extract θ δ hθ hδ hsum
  apply disjoint_of_one
  intro c hc
  let K := hc.toFinset
  obtain ⟨N, hN, P, regular, mass⟩ := pool K.card N₀
  have maps (n : ℕ) (_ : n ∈ P) : c n ∈ K := hc.mem_toFinset.mpr ⟨n, rfl⟩
  obtain ⟨j, _, heavy⟩ := heavy_fibre P K c maps mass
  have hreg (n : ℕ) (hn : n ∈ P.filter (fun n => c n = j)) :=
    regular n (Finset.mem_filter.mp hn).1
  obtain ⟨S, hS, unit⟩ := get N ((le_max_right _ _).trans hN)
    (P.filter fun n => c n = j) hreg heavy
  refine ⟨S, ?_, unit, ?_⟩
  · intro n hn
    exact (le_max_left 2 N₀).trans (hN.trans (hreg n (hS hn)).1)
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨k, hk, rfl⟩
    exact (Finset.mem_filter.mp (hS hi)).2.trans (Finset.mem_filter.mp (hS hk)).2.symm

end OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1
