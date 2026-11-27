import OMAReductions.R_Erdos298_erdos_298_variants_natural_density_R1

-- Credit: @marcusbuffett
-- Thomas Bloom, On a density conjecture about unit fractions.
-- Parameters follow the technical proposition in the unit-fractions formalization.
namespace OMA.R_Erdos298_erdos_298_variants_natural_density_R1_H1_R1

open Finset Filter Real
open scoped Classical

/-- The sieve and normal-order estimates discard an arbitrarily small proportion. -/
def H1 : Prop := ∀ δ : ℝ, 0 < δ → ∃ y z : ℝ, 1 ≤ y ∧ 4*y+4 ≤ z ∧
  ∀ᶠ X : ℕ in atTop, z ≤ (log X) ^ (1/500 : ℝ) ∧
    2/y + (log X) ^ (-(1/200 : ℝ)) ≤ δ ∧
    (((range X).filter fun (n : ℕ) => ¬ ((X : ℝ) ^ (1 - 1 / log (log X)) ≤ n ∧
  (∀ q : ℕ, IsPrimePow q → q ∣ n → (q : ℝ) ≤ (X : ℝ) ^ (1 - 8 / log (log X))) ∧
  (99 / 100 : ℝ) * log (log X) ≤ n.primeFactors.card ∧
  (n.primeFactors.card : ℝ) ≤ 2 * log (log X) ∧
  ∃ u v : ℕ, u ∣ n ∧ v ∣ n ∧ y ≤ u ∧ 4 * u ≤ v ∧ (v : ℝ) ≤ z)).card : ℝ) ≤ δ * X

/-- Bloom's finite reciprocal extraction for smooth, arithmetically regular sets. -/
def H2 : Prop := ∀ᶠ X : ℕ in atTop, ∀ y z : ℝ, 1 ≤ y → 4*y+4 ≤ z →
  z ≤ (log X) ^ (1/500 : ℝ) → ∀ B ⊆ range X, 0 ∉ B →
  (∀ n ∈ B, ((X : ℝ) ^ (1 - 1 / log (log X)) ≤ n ∧
  (∀ q : ℕ, IsPrimePow q → q ∣ n → (q : ℝ) ≤ (X : ℝ) ^ (1 - 8 / log (log X))) ∧
  (99 / 100 : ℝ) * log (log X) ≤ n.primeFactors.card ∧
  (n.primeFactors.card : ℝ) ≤ 2 * log (log X) ∧
  ∃ u v : ℕ, u ∣ n ∧ v ∣ n ∧ y ≤ u ∧ 4 * u ≤ v ∧ (v : ℝ) ≤ z)) →
  2/y + (log X) ^ (-(1/200 : ℝ)) ≤ ∑ n ∈ B, (1 / (n : ℝ)) →
  ∃ d : ℕ, y ≤ d ∧ (d : ℝ) ≤ z ∧ ∃ S ⊆ B, ∑ n ∈ S, (1 / (n : ℚ)) = 1/d

theorem main : H1 → H2 → OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H1 := by
  classical
  intro sieve extract A h0 hpos
  let regular (X : ℕ) (y z : ℝ) (n : ℕ) : Prop :=
    (X : ℝ) ^ (1 - 1 / log (log X)) ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q ∣ n → (q : ℝ) ≤ (X : ℝ) ^ (1 - 8 / log (log X))) ∧
    (99 / 100 : ℝ) * log (log X) ≤ n.primeFactors.card ∧
    (n.primeFactors.card : ℝ) ≤ 2 * log (log X) ∧
    ∃ u v : ℕ, u ∣ n ∧ v ∣ n ∧ y ≤ u ∧ 4 * u ≤ v ∧ (v : ℝ) ≤ z
  let δ := A.upperDensity / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have freq : ∃ᶠ X : ℕ in atTop, 4*δ < A.partialDensity Set.univ X := by
    apply frequently_lt_of_lt_limsup (isCoboundedUnder_le_of_le atTop
      (show ∀ X : ℕ, 0 ≤ A.partialDensity Set.univ X from fun X => by unfold Set.partialDensity; positivity))
    change 4*δ < A.upperDensity
    dsimp [δ]; linarith
  obtain ⟨y,z,hy,hyz,hgood⟩ := sieve δ hδ
  refine ⟨Icc ⌈y⌉₊ ⌊z⌋₊, ?_, ?_⟩
  · intro d hd
    have hh : y ≤ (d : ℝ) := Nat.ceil_le.mp (mem_Icc.mp hd).1
    exact_mod_cast (show (0:ℝ) < d by linarith)
  intro N
  have hsize : ∀ᶠ X : ℕ in atTop, (N : ℝ) ≤ δ * X := by
    exact (tendsto_natCast_atTop_atTop.const_mul_atTop hδ).eventually_ge_atTop _
  obtain ⟨X, hden, ⟨⟨hz,hmass,hbad⟩,htech,hcut,hX⟩⟩ :=
    (freq.and_eventually (hgood.and (extract.and (hsize.and (eventually_ge_atTop 1))))).exists
  have hXp : 0 < (X:ℝ) := by exact_mod_cast (show 0 < X by omega)
  let T := (range X).filter fun n => n ∈ A
  let E := (range X).filter fun n => ¬ regular X y z n
  let B := T \ (range N ∪ E)
  have hT : 4*δ * X < T.card := by
    have setT : A ∩ Set.univ ∩ Set.Iio X = (T : Set ℕ) := by ext n; simp [T, and_comm]
    have setX : Set.univ ∩ Set.Iio X = (range X : Set ℕ) := by ext n; simp
    unfold Set.partialDensity at hden
    rw [setT,setX,Set.ncard_coe_finset,Set.ncard_coe_finset,card_range] at hden
    exact (lt_div_iff₀ hXp).mp hden
  have card : T.card ≤ B.card + (N + E.card) := by
    have s : T ⊆ B ∪ (range N ∪ E) := by intro n hn; by_cases h : n ∈ range N ∪ E <;> simp [B,hn,h]
    calc
      _ ≤ _ := card_le_card s
      _ ≤ _ := card_union_le ..
      _ ≤ _ := Nat.add_le_add_left (by simpa using card_union_le (range N) E) _
  have low : δ * X ≤ B.card := by
    change (E.card : ℝ) ≤ δ * X at hbad
    have hc : (T.card:ℝ) ≤ B.card + ((N : ℝ) + E.card) := by exact_mod_cast card
    linarith
  have props {n : ℕ} (hn : n ∈ B) : n < X ∧ n ∈ A ∧ N ≤ n ∧ regular X y z n := by
    have ⟨ht,hne⟩ := mem_sdiff.mp hn
    obtain ⟨hx,ha⟩ := mem_filter.mp ht
    exact ⟨mem_range.mp hx,ha,Nat.le_of_not_gt (fun h => hne (mem_union_left _ (mem_range.mpr h))),
      of_not_not (fun h => hne (mem_union_right _ (mem_filter.mpr ⟨hx,h⟩)))⟩
  have hrec : δ ≤ ∑ n ∈ B, (1/(n : ℝ)) := calc
    _ ≤ (B.card : ℝ)/X := (le_div_iff₀ hXp).mpr low
    _ = ∑ _n ∈ B, (1/(X:ℝ)) := by simp [div_eq_mul_inv]
    _ ≤ _ := sum_le_sum fun n hn => one_div_le_one_div_of_le
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h => h0 (h ▸ (props hn).2.1)))
      (by exact_mod_cast (props hn).1.le)
  obtain ⟨d,hyd,hdz,S,hS,hr⟩ := htech y z hy hyz hz B
    (fun n hn => mem_range.mpr (props hn).1) (fun h => h0 (props h).2.1)
    (fun _ hn => (props hn).2.2.2) (hmass.trans hrec)
  exact ⟨d,mem_Icc.mpr ⟨Nat.ceil_le.mpr hyd,Nat.le_floor hdz⟩, S,
    fun n hn => ⟨(props (hS hn)).2.1,(props (hS hn)).2.2.1⟩,hr⟩

end OMA.R_Erdos298_erdos_298_variants_natural_density_R1_H1_R1
