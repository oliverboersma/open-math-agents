import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

-- Step of the squares variant of Erdős Problem 338. Credit: @happycamper.
namespace OMA.Squares338

open Erdos338 Filter

lemma orderAtMostFour : HasOrder (Set.range fun k : ℕ => k ^ 2) 4 := by
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  refine ⟨{a ^ 2, b ^ 2, c ^ 2, d ^ 2}, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨a, rfl⟩
    · exact ⟨b, rfl⟩
    · exact ⟨c, rfl⟩
    · exact ⟨d, rfl⟩
  · simp [Multiset.insert_eq_cons]
  · simpa [Multiset.insert_eq_cons, Nat.add_assoc] using h

theorem squareResidue (x : Nat) :
    x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have residues : ∀ r : Fin 8,
      r.val ^ 2 % 8 = 0 ∨ r.val ^ 2 % 8 = 1 ∨ r.val ^ 2 % 8 = 4 := by decide
  have h := residues ⟨x % 8, Nat.mod_lt _ (by decide)⟩
  change (x % 8) ^ 2 % 8 = 0 ∨ (x % 8) ^ 2 % 8 = 1 ∨ (x % 8) ^ 2 % 8 = 4 at h
  simpa only [← Nat.pow_mod] using h

theorem threeSquaresMissSeven (a b c n : Nat) :
    a ^ 2 + (b ^ 2 + c ^ 2) ≠ 8 * n + 7 := by
  rcases squareResidue a with ha | ha | ha <;>
    rcases squareResidue b with hb | hb | hb <;>
    rcases squareResidue c with hc | hc | hc <;> omega

lemma fourLeOrder (k : ℕ) (hk : HasOrder (Set.range fun j : ℕ => j ^ 2) k) : 4 ≤ k := by
  by_contra! hlt
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hk
  obtain ⟨S, hS, hcard, hsum⟩ := hN (8 * N + 7) (by omega)
  -- Pad a representation of length at most three with zero squares.
  let T := S + Multiset.replicate (3 - S.card) 0
  have hTcard : T.card = 3 := by
    simp only [T, Multiset.card_add, Multiset.card_replicate]
    omega
  have hTsq (x : ℕ) (hx : x ∈ T) : x ∈ Set.range fun j : ℕ => j ^ 2 := by
    rcases Multiset.mem_add.mp hx with hs | hz
    · exact hS x hs
    · exact ⟨0, by simp [Multiset.eq_of_mem_replicate hz]⟩
  have hTsum : T.sum = 8 * N + 7 := by simpa [T] using hsum
  obtain ⟨x, y, z, hT⟩ := Multiset.card_eq_three.mp hTcard
  obtain ⟨a, ha⟩ := hTsq x (by simp [hT, Multiset.insert_eq_cons])
  obtain ⟨b, hb⟩ := hTsq y (by simp [hT, Multiset.insert_eq_cons])
  obtain ⟨c, hc⟩ := hTsq z (by simp [hT, Multiset.insert_eq_cons])
  have h : a ^ 2 + (b ^ 2 + c ^ 2) = 8 * N + 7 := by
    simpa [hT, Multiset.insert_eq_cons, ha, hb, hc] using hTsum
  exact threeSquaresMissSeven a b c N h

end OMA.Squares338

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 := by
  change Erdos338.basisOrder (Set.range fun k : ℕ => k ^ 2) = 4
  unfold Erdos338.basisOrder
  apply le_antisymm
  · exact iInf₂_le 4 OMA.Squares338.orderAtMostFour
  · refine le_iInf₂ fun k hk => ?_
    exact_mod_cast OMA.Squares338.fourLeOrder k hk
