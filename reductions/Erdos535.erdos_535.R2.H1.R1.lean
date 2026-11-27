import OMAReductions.R_Erdos535_erdos_535_R2

-- Credit: @LordMike
-- Port of reductions/Erdos535.erdos_535.variants.sunflower_strong.R1.H1.R1.lean by @JamesSlash (PR #736) onto the identical hypothesis statement Erdos535.erdos_535.R2.H1.

/-! The set sunflower bound follows from its word version and a finite coloring argument. -/

namespace OMA.R_Erdos535_erdos_535_R2_H1_R1

def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ (k m : ℕ) (W : Finset (Fin k → Fin m)),
      (∀ w : Fin r → Fin k → Fin m, (∀ i, w i ∈ W) →
        (∀ j, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b) → W.card ≤ D ^ k

def H2 : Prop :=
  ∀ (r k : ℕ), 0 < k → ∀ F : Finset (Finset ℕ), (∀ A ∈ F, A.card = k) →
    (¬ ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset ℕ,
      ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K) →
    ∃ (m : ℕ) (W : Finset (Fin k → Fin m)), F.card ≤ 3 ^ k * W.card ∧
      ∀ w : Fin r → Fin k → Fin m, (∀ i, w i ∈ W) →
        (∀ j, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b

theorem main : H1 → H2 → OMA.R_Erdos535_erdos_535_R2.H1 := by
  unfold H1 H2 OMA.R_Erdos535_erdos_535_R2.H1
  intro hWord hTransfer r hr
  obtain ⟨D, hD, hBound⟩ := hWord r hr
  refine ⟨3 * D, by omega, ?_⟩
  intro k F hUniform hLarge
  by_cases hZero : k = 0
  · subst k
    have hSmall : F.card ≤ 1 := Finset.card_le_one.mpr fun A hA B hB =>
      (Finset.card_eq_zero.mp (hUniform A hA)).trans
        (Finset.card_eq_zero.mp (hUniform B hB)).symm
    simp only [pow_zero] at hLarge
    exact (hLarge.not_ge hSmall).elim
  · by_contra hFree
    obtain ⟨m, W, hSize, hWordFree⟩ := hTransfer r k (Nat.pos_of_ne_zero hZero) F hUniform hFree
    apply hLarge.not_ge
    rw [mul_pow]
    exact hSize.trans (Nat.mul_le_mul_left _ (hBound k m W hWordFree))

end OMA.R_Erdos535_erdos_535_R2_H1_R1
