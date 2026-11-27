import OMAReductions.R_Erdos40_erdos_40_variants_weaker_R1

/-!
# Two cases for lowering a bound on ordered additive representations

When a sum has odd multiplicity, it has a midpoint. Each saturated sum can
therefore be assigned to one midpoint. The first step asks for a selection
retaining half of every positive prefix in this case.

When the cap is even, a set containing two translates of the same dense
subset already has a solution. Moving the right endpoint of each pair
injects its representations into one shifted sum. Moving the left endpoint
with largest first coordinate supplies one further representation.
The second step concerns sets without such a dense translated intersection.

Credit: @NicholasWierenga
-/

namespace Erdos40

open Finset AdditiveCombinatorics

/-- If both a set and a positive translate lie in `A`, every nonempty sum fiber
of the set has strictly fewer representations than the corresponding shifted sum in `A`. -/
theorem sumRep_lt_shift_of_subset_of_pos {A B : Set ℕ} {n d : ℕ}
    (hsub : B ⊆ A) (hshift : ∀ b ∈ B, b + d ∈ A) (hd : 0 < d)
    (hpos : 0 < sumRep B n) : sumRep B n < sumRep A (n + d) := by
  classical
  let shiftSumFiber (S : Set ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
    (_root_.Finset.HasAntidiagonal.antidiagonal m).filter (fun p ↦ p.1 ∈ S ∧ p.2 ∈ S)
  have mem_shiftSumFiber {S : Set ℕ} {m : ℕ} {p : ℕ × ℕ} :
      p ∈ shiftSumFiber S m ↔ p.1 + p.2 = m ∧ p.1 ∈ S ∧ p.2 ∈ S := by
    simp [shiftSumFiber]
  have shiftSumFiber_card (S : Set ℕ) (m : ℕ) :
      (shiftSumFiber S m).card = sumRep S m := (sumRep_def S m).symm
  let fiber := shiftSumFiber B n
  let shiftRight : (ℕ × ℕ) ↪ (ℕ × ℕ) :=
    ⟨fun p ↦ (p.1, p.2 + d), by
      intro p q h
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      exact Prod.ext hfst (Nat.add_right_cancel hsnd)⟩
  have hfiber : fiber.Nonempty :=
    Finset.card_pos.mp (by simpa only [fiber, shiftSumFiber_card] using hpos)
  let firstCoords := fiber.image Prod.fst
  have hcoords : firstCoords.Nonempty := hfiber.image _
  obtain ⟨p, hp, hpmax⟩ := Finset.mem_image.mp (Finset.max'_mem firstCoords hcoords)
  have ⟨hsum, hp₁, hp₂⟩ := mem_shiftSumFiber.mp hp
  have hsubset : fiber.map shiftRight ⊆ shiftSumFiber A (n + d) := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hq
    have ⟨hzsum, hz₁, hz₂⟩ := mem_shiftSumFiber.mp hz
    change (z.1, z.2 + d) ∈ shiftSumFiber A (n + d)
    exact mem_shiftSumFiber.mpr ⟨by dsimp; omega, hsub hz₁, hshift _ hz₂⟩
  let outside := (p.1 + d, p.2)
  have hout : outside ∈ shiftSumFiber A (n + d) :=
    mem_shiftSumFiber.mpr ⟨by dsimp [outside]; omega, hshift _ hp₁, hsub hp₂⟩
  have hout' : outside ∉ fiber.map shiftRight := by
    intro hmem
    obtain ⟨q, hq, heq⟩ := Finset.mem_map.mp hmem
    have hqmax := Finset.le_max' firstCoords q.1 (Finset.mem_image_of_mem _ hq)
    have hqpos : q.1 = p.1 + d := congrArg Prod.fst heq
    omega
  have hstrict : fiber.map shiftRight ⊂ shiftSumFiber A (n + d) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, fun heq ↦ hout' (heq ▸ hout)⟩
  simpa only [fiber, Finset.card_map, shiftSumFiber_card] using Finset.card_lt_card hstrict

/-- Keeping elements with a fixed positive shift companion lowers any positive sum cap by one. -/
theorem sumRep_le_of_subset_of_pos_shift {A B : Set ℕ} {d K : ℕ}
    (hsub : B ⊆ A) (hshift : ∀ b ∈ B, b + d ∈ A) (hd : 0 < d)
    (hcap : ∀ n, sumRep A n ≤ K + 1) : ∀ n, sumRep B n ≤ K := by
  intro n
  by_contra! hn
  have hlt := sumRep_lt_shift_of_subset_of_pos hsub hshift hd
    (show 0 < sumRep B n by omega)
  have hbound := hcap (n + d)
  omega

end Erdos40

open Filter Real Set AdditiveCombinatorics

namespace Erdos40Finite

theorem sqrt_density_of_prefix_domination {A B : Set ℕ}
    (hdom : ∀ n : ℕ, (A ∩ Icc 1 n).ncard ≤ 2 * (B ∩ Icc 1 n).ncard)
    (hA : (fun n : ℕ ↦ √(n : ℝ)) =O[atTop] (fun n ↦ ((A ∩ Icc 1 n).ncard : ℝ))) :
    (fun n : ℕ ↦ √(n : ℝ)) =O[atTop] (fun n ↦ ((B ∩ Icc 1 n).ncard : ℝ)) := by
  apply hA.trans
  apply Asymptotics.IsBigO.of_bound 2
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_natCast]
  exact_mod_cast hdom n

end Erdos40Finite

namespace OMA.R_Erdos40_erdos_40_variants_weaker_R1_H2_R1

/-- Lower an odd ordered cap while retaining at least half of every positive prefix. -/
def H1 : Prop :=
  ∀ h : ℕ, 2 ≤ h → ∀ A : Set ℕ, (∀ n, sumRep A n ≤ 2 * h + 1) →
    ∃ B : Set ℕ, B ⊆ A ∧ (∀ n, sumRep B n ≤ 2 * h) ∧
      ∀ n : ℕ, (A ∩ Icc 1 n).ncard ≤ 2 * (B ∩ Icc 1 n).ncard

/-- Lower an even ordered cap when every positive shift intersection fails the
square-root lower density condition. -/
def H2 : Prop :=
  ∀ g : ℕ, 3 ≤ g → ∀ A : Set ℕ, (∀ n, sumRep A n ≤ 2 * g) →
    ((fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
      (fun n ↦ ((A ∩ Icc 1 n).ncard : ℝ))) →
    (∀ d : ℕ, 0 < d →
      ¬ ((fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
        (fun n ↦ (({x : ℕ | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 n).ncard : ℝ)))) →
    ∃ B : Set ℕ, B ⊆ A ∧ (∀ n, sumRep B n ≤ 2 * g - 1) ∧
      ((fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
        (fun n ↦ ((B ∩ Icc 1 n).ncard : ℝ)))

theorem main : H1 → H2 → OMA.R_Erdos40_erdos_40_variants_weaker_R1.H2 := by
  classical
  intro hOdd hEven k hk A hcap hA
  by_cases heven : k % 2 = 0
  · obtain ⟨h, rfl⟩ : ∃ h : ℕ, k = 2 * h := ⟨k / 2, by omega⟩
    obtain ⟨B, hBA, hcapB, hprefix⟩ := hOdd h (by omega) A hcap
    exact ⟨B, hBA, hcapB, Erdos40Finite.sqrt_density_of_prefix_domination hprefix hA⟩
  · by_cases hex : ∃ d : ℕ, 0 < d ∧
        ((fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
          (fun n ↦ (({x : ℕ | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 n).ncard : ℝ)))
    · obtain ⟨d, hd, hBdense⟩ := hex
      let B : Set ℕ := {x | x ∈ A ∧ x + d ∈ A}
      have hBA : B ⊆ A := fun _ hx ↦ hx.1
      have hshift : ∀ b ∈ B, b + d ∈ A := fun _ hx ↦ hx.2
      exact ⟨B, hBA, Erdos40.sumRep_le_of_subset_of_pos_shift hBA hshift hd hcap, hBdense⟩
    · let g := (k + 1) / 2
      have hg : 3 ≤ g := by dsimp [g]; omega
      have hkg : 2 * g = k + 1 := by dsimp [g]; omega
      have hgk : 2 * g - 1 = k := by omega
      have hcap' : ∀ n, sumRep A n ≤ 2 * g := by simpa only [hkg] using hcap
      obtain ⟨B, hBA, hcapB, hBdense⟩ :=
        hEven g hg A hcap' hA (fun d hd hDense ↦ hex ⟨d, hd, hDense⟩)
      exact ⟨B, hBA, hgk ▸ hcapB, hBdense⟩

end OMA.R_Erdos40_erdos_40_variants_weaker_R1_H2_R1

