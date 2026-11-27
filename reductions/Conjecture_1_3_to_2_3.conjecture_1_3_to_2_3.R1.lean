import FormalConjectures.Wikipedia.conjecture_1_3_to_2_3


-- Reduction Conjecture_1_3_to_2_3.conjecture_1_3_to_2_3.R1 of The $\frac 1 3$–$\frac 2 3$ conjecture
-- Credit: @cepezeta14
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Idea: separar los casos ya demostrados en la literatura del nucleo abierto.
--   H1: ancho a lo sumo 2                         (conocido: Linial 1984)
--   H2: posets 6-delgados (cada elemento incomparable con a lo sumo 6 otros)
--                                                 (conocido: Brightwell-Wright 1992, Peczarski 2008)
--   H3: ancho al menos 3 y algun elemento incomparable con al menos 7 otros   (ABIERTO)

namespace OMA.R_Conjecture_1_3_to_2_3_conjecture_1_3_to_2_3_R1

-- Ancho a lo sumo 2 (Linial 1984).
def H1 : Prop := ∀ (P : Type) [Finite P] [PartialOrder P]
    (not_total : ¬ Std.Total (α := P) (· ≤ ·))
    (width_le_two : ∀ a b c : P, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b)
    (total_ext : Set <| OrderHom P ℕ)
    (total_ext_def : ∀ σ, σ ∈ total_ext ↔ Set.range σ = Set.Icc 1 (Nat.card P)),
    ∃ x y : P, ({σ ∈ total_ext | σ x < σ y}.ncard / total_ext.ncard : ℚ)
      ∈ Set.Icc (1/3) (2/3)

-- Posets 6-delgados (Brightwell-Wright 1992 para 5-delgados, Peczarski 2008 para 6-delgados).
def H2 : Prop := ∀ (P : Type) [Finite P] [PartialOrder P]
    (not_total : ¬ Std.Total (α := P) (· ≤ ·))
    (thin : ∀ x : P, Set.ncard {y : P | ¬ x ≤ y ∧ ¬ y ≤ x} ≤ 6)
    (total_ext : Set <| OrderHom P ℕ)
    (total_ext_def : ∀ σ, σ ∈ total_ext ↔ Set.range σ = Set.Icc 1 (Nat.card P)),
    ∃ x y : P, ({σ ∈ total_ext | σ x < σ y}.ncard / total_ext.ncard : ℚ)
      ∈ Set.Icc (1/3) (2/3)

-- Nucleo abierto: hay una anticadena de tamano 3 y un elemento incomparable con al menos 7 otros.
def H3 : Prop := ∀ (P : Type) [Finite P] [PartialOrder P]
    (not_total : ¬ Std.Total (α := P) (· ≤ ·))
    (three : ∃ a b c : P, ¬ a ≤ b ∧ ¬ b ≤ a ∧ ¬ a ≤ c ∧ ¬ c ≤ a ∧ ¬ b ≤ c ∧ ¬ c ≤ b)
    (fat : ∃ x : P, 7 ≤ Set.ncard {y : P | ¬ x ≤ y ∧ ¬ y ≤ x})
    (total_ext : Set <| OrderHom P ℕ)
    (total_ext_def : ∀ σ, σ ∈ total_ext ↔ Set.range σ = Set.Icc 1 (Nat.card P)),
    ∃ x y : P, ({σ ∈ total_ext | σ x < σ y}.ncard / total_ext.ncard : ℚ)
      ∈ Set.Icc (1/3) (2/3)

theorem main : H1 → H2 → H3 → type_of% @Conjecture_1_3_to_2_3.conjecture_1_3_to_2_3 := by
  intro h1 h2 h3 P hfin hpo not_total total_ext total_ext_def
  by_cases hw : ∀ a b c : P, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b
  · exact h1 P not_total hw total_ext total_ext_def
  · by_cases ht : ∀ x : P, Set.ncard {y : P | ¬ x ≤ y ∧ ¬ y ≤ x} ≤ 6
    · exact h2 P not_total ht total_ext total_ext_def
    · push Not at hw ht
      obtain ⟨a, b, c, hab, hba, hac, hca, hbc, hcb⟩ := hw
      obtain ⟨x, hx⟩ := ht
      exact h3 P not_total ⟨a, b, c, hab, hba, hac, hca, hbc, hcb⟩ ⟨x, by omega⟩
        total_ext total_ext_def

end OMA.R_Conjecture_1_3_to_2_3_conjecture_1_3_to_2_3_R1
