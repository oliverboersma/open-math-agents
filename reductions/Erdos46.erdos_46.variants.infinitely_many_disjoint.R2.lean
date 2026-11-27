import FormalConjectures.ErdosProblems.«46»

-- Credit: @LDJAI
-- Split the finite-color Egyptian-fraction theorem from the selection of a disjoint sequence.

open scoped BigOperators

namespace OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2

/-- One monochromatic block (the Erdős–Graham coloring theorem). -/
def H1 : Prop :=
  ∀ c : ℕ → ℕ, (Set.range c).Finite →
      ∃ s : Finset ℕ, (∀ n ∈ s, 2 ≤ n) ∧ (∑ n ∈ s, (1 / n : ℚ)) = 1 ∧
        (c '' (s : Set ℕ)).Subsingleton

/-- Blocks available beyond every cutoff admit a pairwise disjoint sequence. -/
def H2 : Prop :=
  ∀ P : Finset ℕ → Prop,
    (∀ b : ℕ, ∃ s : Finset ℕ, P s ∧ ∀ n ∈ s, b < n) →
    ∃ S : ℕ → Finset ℕ, (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧ ∀ i, P (S i)

theorem main : H1 → H2 → type_of% @Erdos46.erdos_46.variants.infinitely_many_disjoint := by
  intro oneBlock separated c hc
  classical
  apply separated (fun s => (∀ n ∈ s, 2 ≤ n) ∧
    (∑ n ∈ s, (1 / n : ℚ)) = 1 ∧ (c '' (s : Set ℕ)).Subsingleton)
  intro b
  let d (n : ℕ) := if n ≤ b then n else b + 1 + c n
  have hd : (Set.range d).Finite := by
    apply (((Finset.range (b + 1)).finite_toSet).union (hc.image (fun a => b + 1 + a))).subset
    rintro _ ⟨n, rfl⟩
    by_cases h : n ≤ b
    · exact Or.inl (by simpa [d, h] using Nat.lt_succ_of_le h)
    · exact Or.inr ⟨c n, ⟨n, rfl⟩, by simp [d, h]⟩
  obtain ⟨s, hden, hsum, hmono⟩ := oneBlock d hd
  have same {m n : ℕ} (hm : m ∈ s) (hn : n ∈ s) : d m = d n :=
    hmono ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
  have above (n : ℕ) (hn : n ∈ s) : b < n := by
    by_contra! hnlow
    have heq : s = {n} := by
      ext m
      rw [Finset.mem_singleton]
      constructor
      · intro hm
        have h := same hm hn
        by_cases hmlow : m ≤ b
        · simpa [d, hmlow, hnlow] using h
        · simp only [d, if_neg hmlow, if_pos hnlow] at h
          omega
      · rintro rfl
        exact hn
    have hone : (1 : ℚ) / n = 1 := by simpa [heq] using hsum
    have hgt : (1 : ℚ) < n := by exact_mod_cast (hden n hn : 1 < n)
    exact ((div_lt_one (lt_trans zero_lt_one hgt)).2 hgt).ne hone
  refine ⟨s, ⟨hden, hsum, ?_⟩, above⟩
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
  have h : b + 1 + c m = b + 1 + c n := by
    simpa only [d, if_neg (above m hm).not_ge, if_neg (above n hn).not_ge] using same hm hn
  omega

end OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2
